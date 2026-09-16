//! Bounded original layered grammar; deliberately independent of Pratt precedence.
use super::*;
impl Parser<'_> {
    fn chainl1<T, O>(
        &mut self,
        mut operand: impl FnMut(&mut Self) -> Result<T, ParseError>,
        mut op: impl FnMut(&mut Self) -> Option<O>,
        build: impl Fn(O, T, T) -> T,
    ) -> Result<T, ParseError> {
        let mut lhs = operand(self)?;
        loop {
            let Some(o) = op(self) else { break };
            let rhs = operand(self)?;
            lhs = build(o, lhs, rhs);
        }
        Ok(lhs)
    }
    pub(super) fn iff_reference(&mut self) -> Result<Formula, ParseError> {
        let lhs = self.implies_reference()?;
        if self.try_punct("<=>") || self.try_punct("⇔") {
            let rhs = self.implies_reference()?;
            Ok(Formula::Iff(Box::new(lhs), Box::new(rhs)))
        } else {
            Ok(lhs)
        }
    }
    fn implies_reference(&mut self) -> Result<Formula, ParseError> {
        let lhs = self.disjuncts_reference()?;
        if self.try_punct("==>") || self.try_punct("⇒") {
            let rhs = self.implies_reference()?;
            Ok(Formula::Implies(Box::new(lhs), Box::new(rhs)))
        } else {
            Ok(lhs)
        }
    }
    fn disjuncts_reference(&mut self) -> Result<Formula, ParseError> {
        self.chainl1(
            |p| p.conjuncts_reference(),
            // `|` is also process parallel — but inside formulas it's OR.
            |p| (p.try_punct("|") || p.try_punct("∨")).then_some(()),
            |(), lhs, rhs| Formula::Or(Box::new(lhs), Box::new(rhs)),
        )
    }
    fn conjuncts_reference(&mut self) -> Result<Formula, ParseError> {
        self.chainl1(
            |p| p.negation_reference(),
            |p| (p.try_punct("&") || p.try_punct("∧")).then_some(()),
            |(), lhs, rhs| Formula::And(Box::new(lhs), Box::new(rhs)),
        )
    }
    fn negation_reference(&mut self) -> Result<Formula, ParseError> {
        if self.try_kw("not") || self.try_punct("¬") {
            let f = self.fatom_reference()?;
            Ok(Formula::Not(Box::new(f)))
        } else {
            self.fatom_reference()
        }
    }
    fn fatom_reference(&mut self) -> Result<Formula, ParseError> {
        self.skip_ws();
        if self.try_kw("F") || self.try_punct("⊥") {
            return Ok(Formula::False);
        }
        if self.try_kw("T") || self.try_punct("⊤") {
            return Ok(Formula::True);
        }
        // Quantifiers: All / ∀ / Ex / ∃
        if self.try_kw("All") || self.try_punct("∀") {
            let vs = self.quantifier_binders()?;
            let f = self.iff_reference()?;
            return Ok(Formula::Forall(vs, Box::new(f)));
        }
        if self.try_kw("Ex") || self.try_punct("∃") {
            let vs = self.quantifier_binders()?;
            let f = self.iff_reference()?;
            return Ok(Formula::Exists(vs, Box::new(f)));
        }
        // Try a complete atom before grouping a formula. A grouped term can
        // continue through any of the term grammar's operators before reaching
        // its relation, so inspecting just the next operator is insufficient.
        let start = self.lx.clone();
        let atom = self.formula_atom();
        // Capture lexer diagnostics as well as grammar errors before restoring.
        let atom_error = match self.lx.finish(atom) {
            Ok(formula) => return Ok(formula),
            Err(error) => error,
        };
        self.lx = start;
        if self.try_punct("(") {
            let formula = match self.iff_reference() {
                Ok(formula) => formula,
                Err(error) => return Err(Self::select_alt_error(atom_error, error)),
            };
            // Prefer the formula's closer on ties. A relational parse that
            // progressed further can still explain a truncated formula prefix
            // (for example, `F` parsed as false before an application).
            if let Err(error) = self.require_punct(")") {
                return Err(Self::select_alt_error(error, atom_error));
            }
            if self.at_term_continuation() {
                return Err(atom_error);
            }
            return Ok(formula);
        }
        Err(atom_error)
    }
}
