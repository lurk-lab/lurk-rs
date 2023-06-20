use crate::field::{FWrap, LurkField};
use anyhow::{bail, Result};
use std::collections::HashMap;

use super::{
    constrainer::SlotsIndices, pointers::Ptr, store::Store, symbol::Symbol, tag::Tag, MetaPtr, LEM,
    LEMOP,
};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum SlotType {
    Hash2,
    Hash3,
    Hash4,
}

impl SlotType {
    pub(crate) fn preimg_size(&self) -> usize {
        match self {
            Self::Hash2 => 4,
            Self::Hash3 => 6,
            Self::Hash4 => 8,
        }
    }
}

impl std::fmt::Display for SlotType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Hash2 => write!(f, "Hash2"),
            Self::Hash3 => write!(f, "Hash3"),
            Self::Hash4 => write!(f, "Hash4"),
        }
    }
}

/// This hashmap is populated during interpretation, telling which slots were
/// visited and the pointers that were collected for each of them.
///
/// The pair `(usize, SlotType)` is a pair of slot index and slot type:
///
///```text
///            Slot index
///      ┌────┬───┬───┬───┬───
///      │    │ 0 │ 1 │ 2 │...
///      ├────┼───┼───┼───┼───
/// Slot │ H2 │ a │ b │   │...
/// type ├────┼───┼───┼───┼───
///      │ H3 │   │   │ c │...
///      ├────┼───┼───┼───┼───
///      │... │...│...│...│...
///```
///
/// In the example above, we can see three visited slots:
/// * The slots 0 and 1 for `Hash2`
/// * The slot 2 for `Hash3`
pub(crate) type Visits<F> = HashMap<(usize, SlotType), Vec<Ptr<F>>>;

/// A `Frame` carries the data that results from interpreting a LEM. That is,
/// it contains the input, the output and all the assignments resulting from
/// running one iteration as a HashMap of meta pointers to pointers.
///
/// Finally, `visits` contains the data collected from visiting the slots. This
/// information is used to generte the witness.
#[derive(Clone)]
pub struct Frame<F: LurkField> {
    pub input: [Ptr<F>; 3],
    pub output: [Ptr<F>; 3],
    pub binds: HashMap<MetaPtr, Ptr<F>>,
    pub visits: Visits<F>,
}

impl LEM {
    /// Interprets a LEM using a stack of operations to be popped and executed.
    /// It modifies a `Store` and binds `MetaPtr`s to `Ptr`s as it goes. We also
    /// want to collect data from visited slots.
    fn run<F: LurkField>(
        &self,
        input: [Ptr<F>; 3],
        store: &mut Store<F>,
        slots_indices: &SlotsIndices,
    ) -> Result<Frame<F>> {
        // key/val pairs on this map should never be overwritten
        let mut binds = HashMap::default();
        macro_rules! bind {
            ( $mptr: expr, $ptr: expr ) => {
                if binds.insert($mptr, $ptr).is_some() {
                    bail!("{} already defined", $mptr);
                }
            };
        }

        for (i, name) in self.input.iter().enumerate() {
            bind!(MetaPtr(name.clone()), input[i]);
        }

        let mut visits = Visits::default();

        let mut stack = vec![&self.lem_op];
        while let Some(op) = stack.pop() {
            match op {
                LEMOP::Null(tgt, tag) => {
                    let tgt_ptr = Ptr::null(*tag);
                    bind!(tgt.clone(), tgt_ptr);
                }
                LEMOP::Hash2(tgt, tag, src) => {
                    let src_ptr1 = src[0].get_ptr(&binds)?.to_owned();
                    let src_ptr2 = src[1].get_ptr(&binds)?.to_owned();
                    let tgt_ptr = store.intern_2_ptrs(*tag, src_ptr1, src_ptr2);
                    bind!(tgt.clone(), tgt_ptr);
                    visits.insert(*slots_indices.get(op).unwrap(), vec![src_ptr1, src_ptr2]);
                }
                LEMOP::Hash3(tgt, tag, src) => {
                    let src_ptr1 = src[0].get_ptr(&binds)?.to_owned();
                    let src_ptr2 = src[1].get_ptr(&binds)?.to_owned();
                    let src_ptr3 = src[2].get_ptr(&binds)?.to_owned();
                    let tgt_ptr = store.intern_3_ptrs(*tag, src_ptr1, src_ptr2, src_ptr3);
                    bind!(tgt.clone(), tgt_ptr);
                    visits.insert(
                        *slots_indices.get(op).unwrap(),
                        vec![src_ptr1, src_ptr2, src_ptr3],
                    );
                }
                LEMOP::Hash4(tgt, tag, src) => {
                    let src_ptr1 = src[0].get_ptr(&binds)?.to_owned();
                    let src_ptr2 = src[1].get_ptr(&binds)?.to_owned();
                    let src_ptr3 = src[2].get_ptr(&binds)?.to_owned();
                    let src_ptr4 = src[3].get_ptr(&binds)?.to_owned();
                    let tgt_ptr = store.intern_4_ptrs(*tag, src_ptr1, src_ptr2, src_ptr3, src_ptr4);
                    bind!(tgt.clone(), tgt_ptr);
                    visits.insert(
                        *slots_indices.get(op).unwrap(),
                        vec![src_ptr1, src_ptr2, src_ptr3, src_ptr4],
                    );
                }
                LEMOP::Unhash2(tgts, src) => {
                    let src_ptr = src.get_ptr(&binds)?;
                    let Some(idx) = src_ptr.get_index2() else {
                        bail!("{src} isn't a Tree2 pointer");
                    };
                    let Some((a, b)) = store.fetch_2_ptrs(idx) else {
                        bail!("Couldn't fetch {src}'s children")
                    };
                    bind!(tgts[0].clone(), *a);
                    bind!(tgts[1].clone(), *b);
                    // STEP 2: Update hash_witness with preimage and image
                    visits.insert(*slots_indices.get(op).unwrap(), vec![*a, *b]);
                }
                LEMOP::Unhash3(tgts, src) => {
                    let src_ptr = src.get_ptr(&binds)?;
                    let Some(idx) = src_ptr.get_index3() else {
                        bail!("{src} isn't a Tree3 pointer");
                    };
                    let Some((a, b, c)) = store.fetch_3_ptrs(idx) else {
                        bail!("Couldn't fetch {src}'s children")
                    };
                    bind!(tgts[0].clone(), *a);
                    bind!(tgts[1].clone(), *b);
                    bind!(tgts[2].clone(), *c);
                    // STEP 2: Update hash_witness with preimage and image
                    visits.insert(*slots_indices.get(op).unwrap(), vec![*a, *b, *c]);
                }
                LEMOP::Unhash4(tgts, src) => {
                    let src_ptr = src.get_ptr(&binds)?;
                    let Some(idx) = src_ptr.get_index4() else {
                        bail!("{src} isn't a Tree4 pointer");
                    };
                    let Some((a, b, c, d)) = store.fetch_4_ptrs(idx) else {
                        bail!("Couldn't fetch {src}'s children")
                    };
                    bind!(tgts[0].clone(), *a);
                    bind!(tgts[1].clone(), *b);
                    bind!(tgts[2].clone(), *c);
                    bind!(tgts[3].clone(), *d);
                    // STEP 2: Update hash_witness with preimage and image
                    visits.insert(*slots_indices.get(op).unwrap(), vec![*a, *b, *c, *d]);
                }
                LEMOP::Hide(tgt, sec, src) => {
                    let src_ptr = src.get_ptr(&binds)?;
                    let Ptr::Leaf(Tag::Num, secret) = sec.get_ptr(&binds)? else {
                        bail!("{sec} is not a numeric pointer")
                    };
                    let z_ptr = store.hash_ptr(src_ptr)?;
                    let hash =
                        store
                            .poseidon_cache
                            .hash3(&[*secret, z_ptr.tag.to_field(), z_ptr.hash]);
                    let tgt_ptr = Ptr::comm(hash);
                    store.comms.insert(FWrap::<F>(hash), (*secret, *src_ptr));
                    bind!(tgt.clone(), tgt_ptr);
                }
                LEMOP::Open(tgt_secret, tgt_ptr, comm_or_num) => {
                    match comm_or_num.get_ptr(&binds)? {
                        Ptr::Leaf(Tag::Num, hash) | Ptr::Leaf(Tag::Comm, hash) => {
                            let Some((secret, ptr)) = store.comms.get(&FWrap::<F>(*hash)) else {
                                bail!("No committed data for hash {}", &hash.hex_digits())
                            };
                            bind!(tgt_ptr.clone(), *ptr);
                            bind!(tgt_secret.clone(), Ptr::Leaf(Tag::Num, *secret));
                        }
                        _ => {
                            bail!("{comm_or_num} is not a num/comm pointer")
                        }
                    }
                }
                LEMOP::MatchTag(ptr, cases) => {
                    let ptr = ptr.get_ptr(&binds)?;
                    let ptr_tag = ptr.tag();
                    match cases.get(ptr_tag) {
                        Some(op) => stack.push(op),
                        None => bail!("No match for tag {}", ptr_tag),
                    }
                }
                LEMOP::MatchSymbol(match_ptr, cases, def) => {
                    let ptr = match_ptr.get_ptr(&binds)?;
                    let Some(symbol) = store.fetch_symbol(ptr) else {
                        bail!("Symbol not found for {match_ptr}");
                    };
                    match cases.get(&symbol) {
                        Some(op) => stack.push(op),
                        None => stack.push(def),
                    }
                }
                LEMOP::Seq(ops) => stack.extend(ops.iter().rev()),
                LEMOP::Return(o) => {
                    let output = [
                        *o[0].get_ptr(&binds)?,
                        *o[1].get_ptr(&binds)?,
                        *o[2].get_ptr(&binds)?,
                    ];
                    return Ok(Frame {
                        input,
                        output,
                        binds,
                        visits,
                    });
                }
            }
        }
        bail!("Output not reached");
    }

    /// Calls `run` until the stop contidion is satisfied, using the output of one
    /// iteration as the input of the next one.
    pub fn eval<F: LurkField>(
        &self,
        expr: Ptr<F>,
        store: &mut Store<F>,
        slots_indices: &SlotsIndices,
    ) -> Result<Vec<Frame<F>>> {
        let mut expr = expr;
        let mut env = store.intern_symbol(&Symbol::lurk_sym("nil"));
        let mut cont = Ptr::null(Tag::Outermost);
        let mut frames = vec![];
        let terminal = &Ptr::null(Tag::Terminal);
        let error = &Ptr::null(Tag::Error);
        loop {
            let frame = self.run([expr, env, cont], store, slots_indices)?;
            frames.push(frame.clone());
            if &frame.output[2] == terminal || &frame.output[2] == error {
                break;
            } else {
                [expr, env, cont] = frame.output;
            }
        }
        Ok(frames)
    }
}
