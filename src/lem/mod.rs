//! ## Lurk Evaluation Model (LEM)
//!
//! A LEM is a description of Lurk's evaluation algorithm, encoded as data. In
//! other words, it's a meta-representation of Lurk's step function.
//!
//! The motivation behind LEM is the fact that hand-writing the circuit is a
//! fragile process that hinders experimentation and safety. Thus we would like
//! to bootstrap the circuit automatically, given a higher level description of
//! the step function.
//!
//! LEM also allows the `Store` API to be completely abstracted away from the
//! responsibilities of LEM authors. Indeed, we want the implementation details
//! of the `Store` not to be important at LEM definition time.
//!
//! ### Data semantics
//!
//! A LEM describes how to handle pointers with variables, which are
//! basically named references. Instead of saying `let foo ...` in Rust, we
//! use a `Var("foo")` in LEM.
//!
//! The actual algorithm is encoded with a LEM operation (`LEMOP`). It's worth
//! noting that one of the LEM operators is in fact a vector of operators, which
//! allows imperative/sequenced expressiveness.
//!
//! ### Interpretation
//!
//! Running a LEM is done via interpretation, which might be a bit slower than
//! calling Rust functions directly. But it also has its advantages:
//!
//! 1. The logic to collect data during execution can be factored out from the
//! definition of the step function. This process is needed in order to evidence
//! the inputs for the circuit at proving time;
//!
//! 2. Actually, such logic to collect data is a natural consequence of the fact
//! that we're on a higher level of abstraction. Relevant data is not simply
//! stored on rust variables that die after the function ends. On the contrary,
//! all relevant data lives on data structures that are also a product of the
//! interpreted LEM.
//!
//! ### Constraining
//!
//! This is the process of creating the circuit, which we want to be done
//! automatically for whoever creates a LEM. Each `LEMOP` has to be precisely
//! constrained in such a way that the resulting circuits accepts a witness iff
//! it was generated by a valid interpretation of the LEM at play.
//!
//! ### Static checks of correctness
//!
//! Since a LEM is an algorithm encoded as data, we can perform static checks of
//! correctness as some form of (automated) formal verification. Here are some
//! (WIP) properties we want a LEM to have before we can adopt it as a proper
//! Lurk step function:
//!
//! 1. Non-duplicated input labels: right at the start of interpretation, the
//! input labels are bound to the actual pointers that represent the expression,
//! environment and continuation. If some label is repeated, semantics become
//! confusing;
//!
//! 2. Assign first, use later: this prevents obvious errors such as "x not
//! defined" during interpretation or "x not allocated" during constraining.

mod circuit;
mod eval;
mod interpreter;
mod macros;
mod path;
mod pointers;
mod store;
mod symbol;
mod tag;
mod var_map;

use crate::field::LurkField;
use anyhow::Result;
use indexmap::IndexMap;
use std::sync::Arc;

use self::{path::Path, store::Store, symbol::Symbol, tag::Tag};

pub type AString = Arc<str>;
pub type AVec<A> = Arc<[A]>;

/// A `LEM` has the name for the inputs and its characteristic control node
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Func {
    input_vars: Vec<Var>,
    output_size: usize,
    block: Block,
}

/// Named references to be bound to `Ptr`s.
#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub struct Var(AString);

impl std::fmt::Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Var {
    #[inline]
    pub fn name(&self) -> &AString {
        &self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block {
    ops: Vec<Op>,
    ctrl: Ctrl,
}

/// The basic control nodes for LEM logical paths.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ctrl {
    /// `MatchTag(x, cases)` performs a match on the tag of `x`, considering only
    /// the appropriate `LEM` among the ones provided in `cases`
    MatchTag(Var, IndexMap<Tag, Block>),
    /// `MatchSymbol(x, cases, def)` checks whether `x` matches some symbol among
    /// the ones provided in `cases`. If so, run the corresponding `LEM`. Run
    /// The default `def` `LEM` otherwise
    MatchSymbol(Var, IndexMap<Symbol, Block>, Box<Block>),
    /// `Return(rets)` sets the output to `rets`
    Return(Vec<Var>),
}

/// The atomic operations of LEMs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op {
    /// `Call(ys, f, xs)` binds `ys` to the results of `f` applied to `xs`
    Call(Vec<Var>, Box<Func>, Vec<Var>),
    /// `Null(x, t)` binds `x` to a `Ptr::Leaf(t, F::zero())`
    Null(Var, Tag),
    /// `Hash2(x, t, ys)` binds `x` to a `Ptr` with tag `t` and 2 children `ys`
    Hash2(Var, Tag, [Var; 2]),
    /// `Hash3(x, t, ys)` binds `x` to a `Ptr` with tag `t` and 3 children `ys`
    Hash3(Var, Tag, [Var; 3]),
    /// `Hash4(x, t, ys)` binds `x` to a `Ptr` with tag `t` and 4 children `ys`
    Hash4(Var, Tag, [Var; 4]),
    /// `Unhash2([a, b], x)` binds `a` and `b` to the 2 children of `x`
    Unhash2([Var; 2], Var),
    /// `Unhash3([a, b, c], x)` binds `a`, `b` and `c` to the 3 children of `x`
    Unhash3([Var; 3], Var),
    /// `Unhash4([a, b, c, d], x)` binds `a`, `b`, `c` and `d` to the 4 children of `x`
    Unhash4([Var; 4], Var),
    /// `Hide(x, s, p)` binds `x` to a (comm) `Ptr` resulting from hiding the
    /// payload `p` with (num) secret `s`
    Hide(Var, Var, Var),
    /// `Open(s, p, h)` binds `s` and `p` to the secret and payload (respectively)
    /// of the commitment that resulted on (num or comm) `h`
    Open(Var, Var, Var),
}

impl Ctrl {
    /// Intern all symbol paths that are matched on `MatchSymPath`s
    pub fn intern_matched_symbols<F: LurkField>(&self, store: &mut Store<F>) {
        match self {
            Self::MatchSymbol(_, cases, def) => {
                cases.iter().for_each(|(symbol, block)| {
                    store.intern_symbol(symbol);
                    block.ctrl.intern_matched_symbols(store)
                });
                def.ctrl.intern_matched_symbols(store);
            }
            Self::MatchTag(_, cases) => cases
                .values()
                .for_each(|block| block.ctrl.intern_matched_symbols(store)),
            Self::Return(..) => (),
        }
    }
}

impl Func {
    /// Performs the static checks described in `LEM`'s docstring.
    pub fn check(&self) {
        // TODO
    }

    /// Instantiates a `LEM` with the appropriate transformations to make sure
    /// that constraining will be smooth.
    pub fn new(input_vars: Vec<Var>, output_size: usize, block: Block) -> Result<Func> {
        let func = Func {
            input_vars,
            output_size,
            block,
        };
        func.deconflict()
    }

    /// Intern all symbols that are matched on `MatchSymbol`s
    #[inline]
    pub fn intern_matched_symbols<F: LurkField>(&self, store: &mut Store<F>) {
        self.block.ctrl.intern_matched_symbols(store);
    }

    /// Asserts that all paths were visited by a set of frames. This is mostly
    /// for testing purposes.
    pub fn assert_all_paths_taken(&self, paths: &[Path]) {
        assert_eq!(
            self.block.ctrl.num_paths_taken(paths).unwrap(),
            self.block.ctrl.num_paths()
        );
    }
}

#[cfg(test)]
mod tests {
    use super::circuit::SlotsCounter;
    use super::{store::Store, *};
    use crate::{func, lem::pointers::Ptr};
    use bellperson::util_cs::{test_cs::TestConstraintSystem, Comparable, Delta};
    use blstrs::Scalar as Fr;

    /// Helper function for testing circuit synthesis.
    ///   - `lem` is the input LEM program.
    ///   - `exprs` is a set of input expressions that can exercise different LEM paths,
    ///   therefore this parameter can be used to test circuit uniformity among all the
    ///   provided expressions.
    ///   - `expected_slots` gives the number of expected slots for each type of hash.
    fn synthesize_test_helper(func: &Func, inputs: Vec<Ptr<Fr>>, expected_num_slots: SlotsCounter) {
        let store = &mut Store::default();
        let outermost = Ptr::null(Tag::Outermost);
        let terminal = Ptr::null(Tag::Terminal);
        let error = Ptr::null(Tag::Error);
        let nil = store.intern_symbol(&Symbol::lurk_sym("nil"));
        let stop_cond = |output: &[Ptr<Fr>]| output[2] == terminal || output[2] == error;

        let slots_count = func.block.count_slots();

        assert_eq!(slots_count, expected_num_slots);

        let computed_num_constraints = func.num_constraints::<Fr>(&slots_count);

        let mut cs_prev = None;
        for input in inputs.into_iter() {
            let input = vec![input, nil, outermost];
            let (frames, _) = func.run(input, store, &stop_cond).unwrap();

            let mut cs;

            for frame in frames.clone() {
                cs = TestConstraintSystem::<Fr>::new();
                func.synthesize(&mut cs, store, &slots_count, &frame)
                    .unwrap();
                assert!(cs.is_satisfied());
                assert_eq!(computed_num_constraints, cs.num_constraints());
                if let Some(cs_prev) = cs_prev {
                    // Check for all input expresssions that all frames are uniform.
                    assert_eq!(cs.delta(&cs_prev, true), Delta::Equal);
                }
                cs_prev = Some(cs);
            }
        }
    }

    #[test]
    fn accepts_virtual_nested_match_tag() {
        let lem = func!((expr_in, env_in, cont_in): 3 => {
            match_tag expr_in {
                Num => {
                    let cont_out_terminal: Terminal;
                    return (expr_in, env_in, cont_out_terminal);
                },
                Char => {
                    match_tag expr_in {
                        // This nested match excercises the need to pass on the
                        // information that we are on a virtual branch, because a
                        // constraint will be created for `cont_out_error` and it
                        // will need to be relaxed by an implication with a false
                        // premise.
                        Num => {
                            let cont_out_error: Error;
                            return (env_in, expr_in, cont_out_error);
                        }
                    };
                },
                Sym => {
                    match_tag expr_in {
                        // This nested match exercises the need to relax `popcount`
                        // because there is no match but it's on a virtual path, so
                        // we don't want to be too restrictive and demand that at
                        // least one path must be taken.
                        Char => {
                            return (cont_in, cont_in, cont_in);
                        }
                    };
                }
            };
        })
        .unwrap();

        let inputs = vec![Ptr::num(Fr::from_u64(42))];
        synthesize_test_helper(&lem, inputs, SlotsCounter::default());
    }

    #[test]
    fn resolves_conflicts_of_clashing_names_in_parallel_branches() {
        let lem = func!((expr_in, env_in, cont_in): 3 => {
            match_tag expr_in {
                // This match is creating `cont_out_terminal` on two different
                // branches, which, in theory, would cause troubles at allocation
                // time. We solve this problem by calling `LEMOP::deconflict`,
                // which turns one into `Num.cont_out_terminal` and the other into
                // `Char.cont_out_terminal`.
                Num => {
                    let cont_out_terminal: Terminal;
                    return (expr_in, env_in, cont_out_terminal);
                },
                Char => {
                    let cont_out_terminal: Terminal;
                    return (expr_in, env_in, cont_out_terminal);
                }
            };
        })
        .unwrap();

        let inputs = vec![Ptr::num(Fr::from_u64(42))];
        synthesize_test_helper(&lem, inputs, SlotsCounter::default());
    }

    #[test]
    fn handles_non_ssa() {
        let func = func!((expr_in, env_in, cont_in): 3 => {
            let x: Cons = hash2(expr_in, expr_in);
            // The next line rewrites `x` and it should move on smoothly, matching
            // the expected number of constraints accordingly
            let x: Cons = hash2(x, x);
            let cont_out_terminal: Terminal;
            return (x, x, cont_out_terminal);
        })
        .unwrap();

        let inputs = vec![Ptr::num(Fr::from_u64(42))];
        synthesize_test_helper(&func, inputs, SlotsCounter::new((2, 0, 0)));
    }

    #[test]
    fn test_simple_all_paths_delta() {
        let lem = func!((expr_in, env_in, cont_in): 3 => {
            let cont_out_terminal: Terminal;
            return (expr_in, env_in, cont_out_terminal);
        })
        .unwrap();

        let inputs = vec![Ptr::num(Fr::from_u64(42)), Ptr::char('c')];
        synthesize_test_helper(&lem, inputs, SlotsCounter::default());
    }

    #[test]
    fn test_match_all_paths_delta() {
        let lem = func!((expr_in, env_in, cont_in): 3 => {
            match_tag expr_in {
                Num => {
                    let cont_out_terminal: Terminal;
                    return (expr_in, env_in, cont_out_terminal);
                },
                Char => {
                    let cont_out_error: Error;
                    return (expr_in, env_in, cont_out_error);
                }
            };
        })
        .unwrap();

        let inputs = vec![Ptr::num(Fr::from_u64(42)), Ptr::char('c')];
        synthesize_test_helper(&lem, inputs, SlotsCounter::default());
    }

    #[test]
    fn test_hash_slots() {
        let lem = func!((expr_in, env_in, cont_in): 3 => {
            let x: Cons = hash2(expr_in, env_in);
            let y: Cons = hash3(expr_in, env_in, cont_in);
            let z: Cons = hash4(expr_in, env_in, cont_in, cont_in);
            let t: Terminal;
            let p: Nil;
            match_tag expr_in {
                Num => {
                    let m: Cons = hash2(env_in, expr_in);
                    let n: Cons = hash3(cont_in, env_in, expr_in);
                    let k: Cons = hash4(expr_in, cont_in, env_in, expr_in);
                    return (m, n, t);
                },
                Char => {
                    return (p, p, t);
                },
                Cons => {
                    return (p, p, t);
                },
                Nil => {
                    return (p, p, t);
                }
            };
        })
        .unwrap();

        let inputs = vec![Ptr::num(Fr::from_u64(42)), Ptr::char('c')];
        synthesize_test_helper(&lem, inputs, SlotsCounter::new((2, 2, 2)));
    }

    #[test]
    fn test_unhash_slots() {
        let lem = func!((expr_in, env_in, cont_in): 3 => {
            let x: Cons = hash2(expr_in, env_in);
            let y: Cons = hash3(expr_in, env_in, cont_in);
            let z: Cons = hash4(expr_in, env_in, cont_in, cont_in);
            let t: Terminal;
            let p: Nil;
            match_tag expr_in {
                Num => {
                    let m: Cons = hash2(env_in, expr_in);
                    let n: Cons = hash3(cont_in, env_in, expr_in);
                    let k: Cons = hash4(expr_in, cont_in, env_in, expr_in);
                    let (m1, m2) = unhash2(m);
                    let (n1, n2, n3) = unhash3(n);
                    let (k1, k2, k3, k4) = unhash4(k);
                    return (m, n, t);
                },
                Char => {
                    return (p, p, t);
                },
                Cons => {
                    return (p, p, p);
                },
                Nil => {
                    return (p, p, p);
                }
            };
        })
        .unwrap();

        let inputs = vec![Ptr::num(Fr::from_u64(42)), Ptr::char('c')];
        synthesize_test_helper(&lem, inputs, SlotsCounter::new((3, 3, 3)));
    }

    #[test]
    fn test_unhash_nested_slots() {
        let lem = func!((expr_in, env_in, cont_in): 3 => {
            let x: Cons = hash2(expr_in, env_in);
            let y: Cons = hash3(expr_in, env_in, cont_in);
            let z: Cons = hash4(expr_in, env_in, cont_in, cont_in);
            let t: Terminal;
            let p: Nil;
            match_tag expr_in {
                Num => {
                    let m: Cons = hash2(env_in, expr_in);
                    let n: Cons = hash3(cont_in, env_in, expr_in);
                    let k: Cons = hash4(expr_in, cont_in, env_in, expr_in);
                    let (m1, m2) = unhash2(m);
                    let (n1, n2, n3) = unhash3(n);
                    let (k1, k2, k3, k4) = unhash4(k);
                    match_tag cont_in {
                        Outermost => {
                            let a: Cons = hash2(env_in, expr_in);
                            let b: Cons = hash3(cont_in, env_in, expr_in);
                            let c: Cons = hash4(expr_in, cont_in, env_in, expr_in);
                            return (m, n, t);
                        },
                        Cons => {
                            let d: Cons = hash2(env_in, expr_in);
                            let e: Cons = hash3(cont_in, env_in, expr_in);
                            let f: Cons = hash4(expr_in, cont_in, env_in, expr_in);
                            return (m, n, t);
                        }
                    };
                },
                Char => {
                    return (p, p, t);
                },
                Cons => {
                    return (p, p, p);
                },
                Nil => {
                    return (p, p, p);
                }
            };
        })
        .unwrap();

        let inputs = vec![Ptr::num(Fr::from_u64(42)), Ptr::char('c')];
        synthesize_test_helper(&lem, inputs, SlotsCounter::new((4, 4, 4)));
    }
}
