// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Guarded recursive SAPIC productions with iterative composition.

use super::*;

impl Parser<'_> {
    /// Left-associative parallel / NDC composition.
    pub(super) fn process_body(&mut self) -> Result<Process, ParseError> {
        let mut left = self.action_process()?;
        loop {
            self.skip_ws();
            let comb = if self.try_punct("||") {
                ProcessComb::Parallel
            } else if self.lx.peek() == Some('|') && self.lx.peek2() != Some('|') {
                self.lx.bump();
                self.skip_ws();
                ProcessComb::Parallel
            } else if self.try_punct("+") {
                ProcessComb::Ndc
            } else {
                return Ok(left);
            };
            left = Process::Comb {
                comb,
                left: Box::new(left),
                right: Box::new(self.action_process()?),
            };
        }
    }

    // Sequencing enters only an action; branches and groups allow composition.
    fn action_process(&mut self) -> Result<Process, ParseError> {
        tamarin_utils::stack::ensure_sufficient_stack(|| self.action_process_inner())
    }

    fn action_process_inner(&mut self) -> Result<Process, ParseError> {
        self.skip_ws();
        // Replication
        if self.try_punct("!") {
            let p = self.process_body()?;
            return Ok(Process::Replication(Box::new(p)));
        }
        if self.try_kw("lookup") {
            let t = self.term(false)?;
            self.require_kw("as")?;
            let v = self.var_spec()?;
            self.require_kw("in")?;
            let p = self.process_body()?;
            let q = self.else_process()?;
            return Ok(Process::Comb {
                comb: ProcessComb::Lookup(t, v),
                left: Box::new(p),
                right: Box::new(q),
            });
        }
        if self.try_kw("if") {
            // Try equality: t = t else formula
            let cond = match self.attempt(|p| {
                let t1 = p.term(false)?;
                p.require_punct("=")?;
                let t2 = p.term(false)?;
                Ok(Condition::Eq(t1, t2))
            }) {
                Some(c) => c,
                None => Condition::Formula(self.formula()?),
            };
            self.require_kw("then")?;
            let p = self.process_body()?;
            let q = self.else_process()?;
            return Ok(Process::Comb {
                comb: ProcessComb::Cond(cond),
                left: Box::new(p),
                right: Box::new(q),
            });
        }
        if self.try_kw("let") {
            // `let pat = t [, pat = t]* in p` or with newline-separated
            // bindings (Tamarin's `genericletBlock = many1 definition` has no
            // separator between bindings).
            // HS `genericletBlock = many1 definition` (Let.hs:23-26, see line 24) with
            // `definition = sapicpatternterm <* equalSign <*> sapicterm`. There
            // is no separator between bindings; `many1` greedily reparses a
            // `definition` and backtracks when one fails to parse. We mirror that
            // by attempting another `(pat = val)` binding and restoring on
            // failure.
            let mut bindings: Vec<(Term, Term)> = Vec::new();
            // First binding is required.
            bindings.push(self.let_definition()?);
            loop {
                let _ = self.try_punct(",");
                self.skip_ws();
                if self.at_keyword("in") {
                    break;
                }
                // Try to parse one more binding; backtrack if it doesn't parse
                // (matching `many1`'s greedy-with-backtrack behaviour).
                match self.attempt(|p| p.let_definition()) {
                    Some(b) => bindings.push(b),
                    None => break,
                }
            }
            self.require_kw("in")?;
            let p = self.process_body()?;
            let q = self.else_process()?;
            // Right-fold the bindings into nested Let combinators.
            let mut acc = p;
            let mut bindings = bindings.into_iter();
            let (pat, value) = bindings.next().expect("let requires a binding");
            for (pat, val) in bindings.rev() {
                acc = Process::Comb {
                    comb: ProcessComb::Let { pat, value: val },
                    left: Box::new(acc),
                    right: Box::new(q.clone()),
                };
            }
            return Ok(Process::Comb {
                comb: ProcessComb::Let { pat, value },
                left: Box::new(acc),
                right: Box::new(q),
            });
        }
        // null process
        if self.try_punct("0") {
            return Ok(Process::Null);
        }
        // Parenthesised process — possibly with `@ term` annotation.
        if self.try_punct("(") {
            let p = self.process_body()?;
            self.require_punct(")")?;
            if self.try_punct("@") {
                let m = self.term(false)?;
                return Ok(Process::AtAnnotation(Box::new(p), m));
            }
            return Ok(p);
        }
        // Sapic action: new / insert / delete / in / out / lock / unlock / event / msr
        let save = self.save();
        if let Some(act) = self.try_sapic_action()? {
            // Optional `; rest` (sequencing)
            let body = if self.try_punct(";") {
                self.action_process()?
            } else {
                Process::Null
            };
            return Ok(Process::Action {
                action: act,
                body: Box::new(body),
            });
        }
        self.restore(save);
        // Process call by name: ident or ident(args)
        let save2 = self.save();
        if let Some(id) = self.lx.identifier() {
            // Heuristic: if followed by `(`, parse as call args.
            self.skip_ws();
            let opening = self.save();
            let args = if self.try_punct("(") {
                // HS `parens $ commaSep (msetterm ...)`
                // (Theory/Text/Parser/Sapic.hs:224-312, see line 296):
                // trailing comma before `)` is permitted.
                self.sep_end_by(opening, ")", |p| p.term(false))?
            } else {
                vec![]
            };
            return Ok(Process::Call { name: id, args });
        }
        self.restore(save2);
        Err(self.err_expect_here("process"))
    }

    fn else_process(&mut self) -> Result<Process, ParseError> {
        if self.try_kw("else") {
            self.process_body()
        } else {
            Ok(Process::Null)
        }
    }
}
