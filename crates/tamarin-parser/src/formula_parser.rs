// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Explicit continuations for formula precedence, binders and ambiguous grouping.
//! Preserves the grammar in Theory/Text/Parser/Formula.hs:61-109.

use super::*;

pub(super) enum Binary {
    And,
    Or,
    Implies,
    Iff,
}
impl Binary {
    fn build(self, left: Formula, right: Formula) -> Formula {
        let (left, right) = (Box::new(left), Box::new(right));
        match self {
            Self::And => Formula::And(left, right),
            Self::Or => Formula::Or(left, right),
            Self::Implies => Formula::Implies(left, right),
            Self::Iff => Formula::Iff(left, right),
        }
    }
}

pub(super) enum Frame {
    Iff,
    IffRest,
    Expr(u8),
    Infix(u8),
    Join(Binary, Option<u8>),
    Atom,
    Not,
    Quantifier(bool, Vec<VarSpec>),
    Group(Box<ParseError>),
}

impl Parser<'_> {
    pub(super) fn iterative_formula(&mut self) -> Result<Formula, ParseError> {
        let mut frames = std::mem::take(&mut self.formula_frames);
        let mut operands = std::mem::take(&mut self.formula_operands);
        let mut next = Some(Frame::Iff);
        let result = (|| {
            while let Some(frame) = next.take().or_else(|| frames.pop()) {
                match frame {
                    Frame::Iff => {
                        frames.push(Frame::IffRest);
                        next = Some(Frame::Expr(1));
                    }
                    Frame::IffRest => {
                        // Equivalence is non-associative: its RHS excludes iff.
                        if self.try_punct("<=>") || self.try_punct("⇔") {
                            frames.push(Frame::Join(Binary::Iff, None));
                            next = Some(Frame::Expr(1));
                        }
                    }
                    Frame::Expr(min) => {
                        if min <= 3 {
                            frames.push(Frame::Infix(min));
                        }
                        if self.try_kw("not") || self.try_punct("¬") {
                            frames.push(Frame::Not);
                        }
                        next = Some(Frame::Atom);
                    }
                    Frame::Infix(min) => {
                        self.skip_ws();
                        let operator = match self.lx.peek() {
                            Some('&') if min <= 3 => Some(("&", Binary::And, 4)),
                            Some('∧') if min <= 3 => Some(("∧", Binary::And, 4)),
                            Some('|') if min <= 2 => Some(("|", Binary::Or, 3)),
                            Some('∨') if min <= 2 => Some(("∨", Binary::Or, 3)),
                            Some('=') if min <= 1 => Some(("==>", Binary::Implies, 1)),
                            Some('⇒') if min <= 1 => Some(("⇒", Binary::Implies, 1)),
                            _ => None,
                        }
                        .and_then(|(token, op, right_min)| {
                            self.try_punct(token).then_some((op, right_min))
                        });
                        if let Some((op, right_min)) = operator {
                            // The right-associative RHS already consumes the
                            // implication chain; only left-associative operators resume.
                            let resume = (!matches!(op, Binary::Implies)).then_some(min);
                            frames.push(Frame::Join(op, resume));
                            next = Some(Frame::Expr(right_min));
                        }
                    }
                    Frame::Join(op, min) => {
                        let right = operands.pop().unwrap();
                        let left = operands.last_mut().unwrap();
                        let value = std::mem::replace(&mut *left, Formula::False);
                        *left = op.build(value, right);
                        next = min.map(Frame::Infix);
                    }
                    Frame::Not => {
                        let top = operands.last_mut().unwrap();
                        let value = std::mem::replace(&mut *top, Formula::False);
                        *top = Formula::Not(Box::new(value));
                    }
                    Frame::Quantifier(all, vars) => {
                        let top = operands.last_mut().unwrap();
                        let value = Box::new(std::mem::replace(&mut *top, Formula::False));
                        *top = if all {
                            Formula::Forall(vars, value)
                        } else {
                            Formula::Exists(vars, value)
                        };
                    }
                    Frame::Atom => {
                        self.skip_ws();
                        if self.try_kw("F") || self.try_punct("⊥") {
                            operands.push(Formula::False);
                        } else if self.try_kw("T") || self.try_punct("⊤") {
                            operands.push(Formula::True);
                        } else if self.try_kw("All") || self.try_punct("∀") {
                            frames.push(Frame::Quantifier(true, self.quantifier_binders()?));
                            next = Some(Frame::Iff);
                        } else if self.try_kw("Ex") || self.try_punct("∃") {
                            frames.push(Frame::Quantifier(false, self.quantifier_binders()?));
                            next = Some(Frame::Iff);
                        } else {
                            // A parenthesised term can continue into a relation.
                            // Preserve the failed atom's error while trying a group.
                            let start = self.lx.clone();
                            let atom = self.formula_atom();
                            let error = match self.lx.finish(atom) {
                                Ok(formula) => {
                                    operands.push(formula);
                                    continue;
                                }
                                Err(error) => error,
                            };
                            self.lx = start;
                            if !self.try_punct("(") {
                                return Err(error);
                            }
                            frames.push(Frame::Group(Box::new(error)));
                            next = Some(Frame::Iff);
                        }
                    }
                    Frame::Group(atom_error) => {
                        if let Err(error) = self.require_punct(")") {
                            return Err(Self::select_alt_error(error, *atom_error));
                        }
                        if self.at_term_continuation() {
                            return Err(*atom_error);
                        }
                    }
                }
            }
            Ok(operands.pop().unwrap())
        })();
        let result = result.map_err(|mut error| {
            for frame in frames.drain(..).rev() {
                if let Frame::Group(atom_error) = frame {
                    error = Self::select_alt_error(*atom_error, error);
                }
            }
            error
        });
        frames.clear();
        self.formula_frames = frames;
        operands.clear();
        self.formula_operands = operands;
        result
    }
}
