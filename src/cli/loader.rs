use std::io;
use std::path::Path;
use std::sync::Arc;

use anyhow::{bail, Context, Error, Result};

use lurk::error::LurkError;
use lurk::eval::lang::Lang;
use lurk::eval::Evaluator;
use lurk::expr::Expression;
use lurk::field::LurkField;
use lurk::parser;
use lurk::ptr::{ContPtr, Ptr};
use lurk::public_parameters::Claim;
use lurk::store::Store;
use lurk::tag::ContTag;
use lurk::writer::Write;
use lurk::{coprocessor::Coprocessor, eval::IO};
use rustyline::{
    error::ReadlineError,
    history::DefaultHistory,
    validate::{MatchingBracketValidator, ValidationContext, ValidationResult, Validator},
    Editor,
};
use rustyline_derive::{Completer, Helper, Highlighter, Hinter};

use super::prove_and_verify::prove_claim;

#[derive(Completer, Helper, Highlighter, Hinter)]
struct InputValidator {
    brackets: MatchingBracketValidator,
}

impl Validator for InputValidator {
    fn validate(&self, ctx: &mut ValidationContext<'_>) -> rustyline::Result<ValidationResult> {
        self.brackets.validate(ctx)
    }
}

pub struct Loader<F: LurkField, C: Coprocessor<F>> {
    pub store: Store<F>,
    pub env: Ptr<F>,
    pub limit: usize,
    pub lang: Arc<Lang<F, C>>,
    pub last_claim: Option<Claim<F>>,
}

impl<F: LurkField, C: Coprocessor<F>> Loader<F, C> {
    pub fn new(store: Store<F>, env: Ptr<F>, limit: usize) -> Loader<F, C> {
        Loader {
            store,
            env,
            limit,
            lang: Arc::new(Lang::<F, C>::new()),
            last_claim: None,
        }
    }

    fn eval_expr(&mut self, expr_ptr: Ptr<F>) -> Result<(Ptr<F>, usize, ContPtr<F>, Vec<Ptr<F>>)> {
        let (io, iterations, emitted) =
            Evaluator::new(expr_ptr, self.env, &mut self.store, self.limit, &self.lang).eval()?;

        let IO {
            expr: result,
            env: _,
            cont: next_cont,
        } = io;

        if next_cont == self.store.get_cont_error() {
            Err(LurkError::IO(io))?
        } else {
            Ok((result, iterations, next_cont, emitted))
        }
    }

    fn handle_meta(&mut self, expr_ptr: Ptr<F>, pwd_path: &Path) -> Result<()> {
        let expr = self.store.fetch(&expr_ptr).ok_or_else(|| Error::msg(""))?;

        let res = match expr {
            Expression::Cons(car, rest) => match &self.store.fetch(&car).unwrap() {
                Expression::Sym(..) => {
                    let s = &self
                        .store
                        .fetch_sym(&car)
                        .ok_or_else(|| Error::msg("handle_meta fetch symbol"))?;
                    match format!("{}", s).as_str() {
                        "assert" => {
                            let (first, rest) = &self.store.car_cdr(&rest)?;
                            assert!(rest.is_nil());
                            let (first_evaled, _, _, _) = self
                                .eval_expr(*first)
                                .with_context(|| "evaluating first arg")?;
                            assert!(!first_evaled.is_nil());
                            None
                        }
                        "assert-eq" => {
                            let (first, rest) = &self.store.car_cdr(&rest)?;
                            let (second, rest) = &self.store.car_cdr(rest)?;
                            assert!(rest.is_nil());
                            let (first_evaled, _, _, _) = self
                                .eval_expr(*first)
                                .with_context(|| "evaluating first arg")?;
                            let (second_evaled, _, _, _) = self
                                .eval_expr(*second)
                                .with_context(|| "evaluating second arg")?;
                            assert!(
                                &self.store.ptr_eq(&first_evaled, &second_evaled)?,
                                "Assertion failed {:?} = {:?},\n {:?} != {:?}",
                                first.fmt_to_string(&self.store),
                                second.fmt_to_string(&self.store),
                                first_evaled.fmt_to_string(&self.store),
                                second_evaled.fmt_to_string(&self.store)
                            );
                            None
                        }
                        "assert-emitted" => {
                            let (first, rest) = &self.store.car_cdr(&rest)?;
                            let (second, rest) = &self.store.car_cdr(rest)?;

                            assert!(rest.is_nil());
                            let (first_evaled, _, _, _) = self.eval_expr(*first)?;
                            let (_, _, _, emitted) = self
                                .eval_expr(*second)
                                .with_context(|| "evaluating first arg")?;
                            let (mut first_emitted, mut rest_emitted) =
                                &self.store.car_cdr(&first_evaled)?;
                            for (i, elem) in emitted.iter().enumerate() {
                                if elem != &first_emitted {
                                    panic!(
                                            ":ASSERT-EMITTED failed at position {}. Expected {}, but found {}.",
                                            i,
                                            first_emitted.fmt_to_string(&self.store),
                                            elem.fmt_to_string(&self.store),
                                        );
                                }
                                (first_emitted, rest_emitted) =
                                    self.store.car_cdr(&rest_emitted)?;
                            }
                            None
                        }
                        "assert-error" => {
                            let (first, rest) = &self.store.car_cdr(&rest)?;
                            assert!(rest.is_nil());
                            assert!(self.eval_expr(*first).is_err());
                            None
                        }
                        "clear" => {
                            self.env = self.store.nil();
                            None
                        }
                        "def" => {
                            // Extends env with a non-recursive binding.
                            //
                            // This: !(:def foo (lambda () 123))
                            //
                            // Gets macroexpanded to this: (let ((foo (lambda () 123)))
                            //                               (current-env))
                            //
                            // And the state's env is set to the result.
                            let (first, rest) = &self.store.car_cdr(&rest)?;
                            let (second, rest) = &self.store.car_cdr(rest)?;
                            assert!(rest.is_nil());
                            let l = &self.store.lurk_sym("let");
                            let current_env = &self.store.lurk_sym("current-env");
                            let binding = &self.store.list(&[*first, *second]);
                            let bindings = &self.store.list(&[*binding]);
                            let current_env_call = &self.store.list(&[*current_env]);
                            let expanded = &self.store.list(&[*l, *bindings, *current_env_call]);
                            let (expanded_evaled, _, _, _) = self.eval_expr(*expanded)?;

                            self.env = expanded_evaled;

                            let (new_binding, _) = &self.store.car_cdr(&expanded_evaled)?;
                            let (new_name, _) = self.store.car_cdr(new_binding)?;
                            Some(new_name)
                        }
                        "defrec" => {
                            // Extends env with a recursive binding.
                            //
                            // This: !(:def foo (lambda () 123))
                            //
                            // Gets macroexpanded to this: (letrec ((foo (lambda () 123)))
                            //                               (current-env))
                            //
                            // And the state's env is set to the result.
                            let (first, rest) = &self.store.car_cdr(&rest)?;
                            let (second, rest) = &self.store.car_cdr(rest)?;
                            assert!(rest.is_nil());
                            let l = &self.store.lurk_sym("letrec");
                            let current_env = &self.store.lurk_sym("current-env");
                            let binding = &self.store.list(&[*first, *second]);
                            let bindings = &self.store.list(&[*binding]);
                            let current_env_call = &self.store.list(&[*current_env]);
                            let expanded = &self.store.list(&[*l, *bindings, *current_env_call]);
                            let (expanded_evaled, _, _, _) = self.eval_expr(*expanded)?;

                            self.env = expanded_evaled;

                            let (new_binding_outer, _) = &self.store.car_cdr(&expanded_evaled)?;
                            let (new_binding_inner, _) = &self.store.car_cdr(new_binding_outer)?;
                            let (new_name, _) = self.store.car_cdr(new_binding_inner)?;
                            Some(new_name)
                        }
                        "load" => {
                            let car = &self.store.car(&rest)?;
                            match &self.store.fetch(car).unwrap() {
                                Expression::Str(..) => {
                                    let path = &self
                                        .store
                                        .fetch_string(car)
                                        .ok_or_else(|| Error::msg("handle_meta fetch_string"))?;
                                    let joined = pwd_path.join(Path::new(&path));
                                    self.load_file(&joined)?
                                }
                                _ => bail!("Argument to LOAD must be a string."),
                            }
                            io::Write::flush(&mut io::stdout()).unwrap();
                            None
                        }
                        "set-env" => {
                            // The state's env is set to the result of evaluating the first argument.
                            let (first, rest) = &self.store.car_cdr(&rest)?;
                            assert!(rest.is_nil());
                            let (first_evaled, _, _, _) = self.eval_expr(*first)?;
                            self.env = first_evaled;
                            None
                        }
                        _ => {
                            bail!("Unsupported command: {}", car.fmt_to_string(&self.store));
                        }
                    }
                }
                _ => bail!("Unsupported command: {}", car.fmt_to_string(&self.store)),
            },
            _ => bail!(
                "Unsupported meta form: {}",
                expr_ptr.fmt_to_string(&self.store)
            ),
        };

        if let Some(expr) = res {
            let mut handle = io::stdout().lock();
            expr.fmt(&self.store, &mut handle)?;

            // TODO: Why is this seemingly necessary to flush?
            // This doesn't work: io::stdout().flush().unwrap();
            // We don't really want the newline.
            println!();
        };

        io::Write::flush(&mut io::stdout()).unwrap();
        Ok(())
    }

    fn handle_non_meta(&mut self, expr_ptr: Ptr<F>) -> Result<(IO<F>, IO<F>, usize)> {
        match Evaluator::new(expr_ptr, self.env, &mut self.store, self.limit, &self.lang).eval() {
            Ok((output, iterations, _)) => {
                let IO {
                    expr: result,
                    env: _,
                    cont: next_cont,
                } = output;
                {
                    if iterations != 1 {
                        print!("[{iterations} iterations] => ");
                    } else {
                        print!("[1 iteration] => ");
                    }

                    let input = IO {
                        expr: expr_ptr,
                        env: self.env,
                        cont: self.store.get_cont_outermost(),
                    };

                    match next_cont.tag {
                        ContTag::Outermost | ContTag::Terminal => {
                            let mut handle = io::stdout().lock();

                            result.fmt(&self.store, &mut handle)?;

                            println!();
                        }
                        ContTag::Error => println!("ERROR!"),
                        _ => println!("Computation incomplete after limit: {}", self.limit),
                    }

                    Ok((input, output, iterations))
                }
            }
            Err(e) => {
                println!("Evaluation error: {e:?}");
                Err(e.into())
            }
        }
    }

    pub fn load_file(&mut self, _path: &Path) -> Result<()> {
        Ok(())
    }

    pub fn repl(&mut self) -> Result<()> {
        println!("Lurk REPL welcomes you.");

        let pwd_path = std::env::current_dir()?;

        let mut editor: Editor<InputValidator, DefaultHistory> = Editor::new()?;

        loop {
            match editor.readline("> ") {
                Ok(line) => {
                    let input = parser::Span::new(&line);
                    #[cfg(not(target_arch = "wasm32"))]
                    match self.store.read_maybe_meta(input) {
                        Ok((_, expr_ptr, is_meta)) => {
                            if is_meta {
                                if let Err(e) = self.handle_meta(expr_ptr, &pwd_path) {
                                    println!("!Error: {e:?}");
                                };
                                continue;
                            } else {
                                if let Err(e) = self.handle_non_meta(expr_ptr) {
                                    println!("REPL Error: {e:?}");
                                }
                                continue;
                            }
                        }
                        Err(parser::Error::NoInput) => {
                            continue;
                        }
                        Err(e) => {
                            println!("Read error: {e:?}")
                        }
                    }
                }
                Err(ReadlineError::Interrupted | ReadlineError::Eof) => {
                    println!("Exiting...");
                    break;
                }
                Err(err) => {
                    println!("Error: {err:?}");
                    break;
                }
            }
        }
        Ok(())
    }

    pub fn prove_last_claim(&mut self) -> Result<()> {
        match &self.last_claim {
            Some(claim) => {
                let _ = prove_claim(claim);
                Ok(())
            }
            None => {
                bail!("No claim to prove");
            }
        }
    }
}
