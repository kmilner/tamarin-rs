// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Explicit continuations for SAPIC actions, branches and composition.

use super::*;

pub(super) enum Frame {
    // Whole-process entries allow composition; sequencing enters only an action.
    Head(bool),
    Chain,
    ChainJoin(bool),
    Replication,
    Group,
    Action,
    Else,
    Join,
    LetElse(Vec<(Term, Term)>),
    LetJoin(Vec<(Term, Term)>),
}

// Keep large payloads out of the frequently pushed bookkeeping frames.
pub(super) enum Value {
    Tree(Process),
    Action(SapicAction),
    Comb(ProcessComb),
}

impl Value {
    fn pop_tree(values: &mut Vec<Self>) -> Process {
        match values.pop().unwrap() {
            Self::Tree(tree) => tree,
            _ => unreachable!("expected process operand"),
        }
    }
}

impl Parser<'_> {
    pub(super) fn iterative_process(&mut self) -> Result<Process, ParseError> {
        let mut frames = std::mem::take(&mut self.process_frames);
        let mut values = std::mem::take(&mut self.process_values);
        let mut next = Some(Frame::Head(true));
        let result = (|| {
            while let Some(frame) = next.take().or_else(|| frames.pop()) {
                match frame {
                    Frame::Head(chain) => {
                        if chain {
                            frames.push(Frame::Chain);
                        }
                        next = self.process_head(&mut frames, &mut values)?;
                    }
                    Frame::Chain => {
                        self.skip_ws();
                        let ndc = if self.try_punct("||") {
                            Some(false)
                        } else if self.lx.peek() == Some('|') && self.lx.peek2() != Some('|') {
                            self.lx.bump();
                            self.skip_ws();
                            Some(false)
                        } else if self.try_punct("+") {
                            Some(true)
                        } else {
                            None
                        };
                        if let Some(ndc) = ndc {
                            frames.push(Frame::ChainJoin(ndc));
                            next = Some(Frame::Head(false));
                        }
                    }
                    Frame::ChainJoin(ndc) => {
                        let right = Value::pop_tree(&mut values);
                        let left = Value::pop_tree(&mut values);
                        let op = if ndc {
                            ProcessComb::Ndc
                        } else {
                            ProcessComb::Parallel
                        };
                        values.push(Value::Tree(Process::Comb {
                            comb: op,
                            left: Box::new(left),
                            right: Box::new(right),
                        }));
                        next = Some(Frame::Chain);
                    }
                    Frame::Replication => {
                        let p = Value::pop_tree(&mut values);
                        values.push(Value::Tree(Process::Replication(Box::new(p))));
                    }
                    Frame::Group => {
                        self.require_punct(")")?;
                        if self.try_punct("@") {
                            let m = self.term(false)?;
                            let p = Value::pop_tree(&mut values);
                            values.push(Value::Tree(Process::AtAnnotation(Box::new(p), m)));
                        }
                    }
                    Frame::Action => {
                        let body = Value::pop_tree(&mut values);
                        let Value::Action(action) = values.pop().unwrap() else {
                            unreachable!("expected action prefix")
                        };
                        values.push(Value::Tree(Process::Action {
                            action,
                            body: Box::new(body),
                        }));
                    }
                    Frame::Else => {
                        frames.push(Frame::Join);
                        next = self.process_else(&mut values);
                    }
                    Frame::Join => {
                        let right = Value::pop_tree(&mut values);
                        let left = Value::pop_tree(&mut values);
                        let Value::Comb(comb) = values.pop().unwrap() else {
                            unreachable!("expected branch prefix")
                        };
                        values.push(Value::Tree(Process::Comb {
                            comb,
                            left: Box::new(left),
                            right: Box::new(right),
                        }));
                    }
                    Frame::LetElse(bindings) => {
                        frames.push(Frame::LetJoin(bindings));
                        next = self.process_else(&mut values);
                    }
                    Frame::LetJoin(bindings) => {
                        let q = Value::pop_tree(&mut values);
                        let mut acc = Value::pop_tree(&mut values);
                        for (pat, val) in bindings.into_iter().rev() {
                            acc = Process::Comb {
                                comb: ProcessComb::Let { pat, value: val },
                                left: Box::new(acc),
                                right: Box::new(q.clone()),
                            };
                        }
                        values.push(Value::Tree(acc));
                    }
                }
            }
            Ok(Value::pop_tree(&mut values))
        })();
        frames.clear();
        values.clear();
        self.process_frames = frames;
        self.process_values = values;
        result
    }

    fn process_else(&mut self, values: &mut Vec<Value>) -> Option<Frame> {
        if self.try_kw("else") {
            Some(Frame::Head(true))
        } else {
            values.push(Value::Tree(Process::Null));
            None
        }
    }

    fn process_head(
        &mut self,
        frames: &mut Vec<Frame>,
        values: &mut Vec<Value>,
    ) -> Result<Option<Frame>, ParseError> {
        self.skip_ws();
        // Replication
        if self.try_punct("!") {
            frames.push(Frame::Replication);
            return Ok(Some(Frame::Head(true)));
        }
        if self.try_kw("lookup") {
            let t = self.term(false)?;
            self.require_kw("as")?;
            let v = self.var_spec()?;
            self.require_kw("in")?;
            values.push(Value::Comb(ProcessComb::Lookup(t, v)));
            frames.push(Frame::Else);
            return Ok(Some(Frame::Head(true)));
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
            values.push(Value::Comb(ProcessComb::Cond(cond)));
            frames.push(Frame::Else);
            return Ok(Some(Frame::Head(true)));
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
            frames.push(Frame::LetElse(bindings));
            return Ok(Some(Frame::Head(true)));
        }
        // null process
        if self.try_punct("0") {
            values.push(Value::Tree(Process::Null));
            return Ok(None);
        }
        // Parenthesised process — possibly with `@ term` annotation.
        if self.try_punct("(") {
            frames.push(Frame::Group);
            return Ok(Some(Frame::Head(true)));
        }
        // Sapic action: new / insert / delete / in / out / lock / unlock / event / msr
        let save = self.save();
        if let Some(act) = self.try_sapic_action()? {
            values.push(Value::Action(act));
            frames.push(Frame::Action);
            return Ok(if self.try_punct(";") {
                Some(Frame::Head(false))
            } else {
                values.push(Value::Tree(Process::Null));
                None
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
            values.push(Value::Tree(Process::Call { name: id, args }));
            return Ok(None);
        }
        self.restore(save2);
        Err(self.err_expect_here("process"))
    }
}
