// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Guarded formula grammar with indexed, lazy ambiguous grouping.
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

impl Parser<'_> {
    pub(super) fn formula_body(&mut self) -> Result<Formula, ParseError> {
        self.formula_iff(&mut tamarin_utils::FastMap::default())
    }

    fn formula_iff(
        &mut self,
        groups: &mut tamarin_utils::FastMap<usize, Pos>,
    ) -> Result<Formula, ParseError> {
        let left = self.formula_expr(1, groups)?;
        if self.try_punct("<=>") || self.try_punct("⇔") {
            Ok(Binary::Iff.build(left, self.formula_expr(1, groups)?))
        } else {
            Ok(left)
        }
    }

    fn formula_expr(
        &mut self,
        min: u8,
        groups: &mut tamarin_utils::FastMap<usize, Pos>,
    ) -> Result<Formula, ParseError> {
        tamarin_utils::stack::ensure_sufficient_stack(|| {
            // The grammar permits one negation before an atom.
            let negated = self.try_kw("not") || self.try_punct("¬");
            let mut left = self.formula_primary(groups)?;
            if negated {
                left = Formula::Not(Box::new(left));
            }
            loop {
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
                let Some((op, right_min)) = operator else {
                    return Ok(left);
                };
                let implication = matches!(op, Binary::Implies);
                left = op.build(left, self.formula_expr(right_min, groups)?);
                if implication {
                    return Ok(left);
                }
            }
        })
    }

    fn formula_primary(
        &mut self,
        groups: &mut tamarin_utils::FastMap<usize, Pos>,
    ) -> Result<Formula, ParseError> {
        self.skip_ws();
        if self.try_kw("F") || self.try_punct("⊥") {
            return Ok(Formula::False);
        }
        if self.try_kw("T") || self.try_punct("⊤") {
            return Ok(Formula::True);
        }
        let all = if self.try_kw("All") || self.try_punct("∀") {
            Some(true)
        } else if self.try_kw("Ex") || self.try_punct("∃") {
            Some(false)
        } else {
            None
        };
        if let Some(all) = all {
            let vars = self.quantifier_binders()?;
            let body = Box::new(self.formula_iff(groups)?);
            return Ok(if all {
                Formula::Forall(vars, body)
            } else {
                Formula::Exists(vars, body)
            });
        }
        // Keep term/group disambiguation indexed and the atom alternative lazy.
        let lazy = self.peek_punct("(") && !self.group_is_term(groups);
        let start = self.lx.clone();
        let atom_error = if lazy {
            None
        } else {
            let atom = self.formula_atom();
            let error = match self.lx.finish(atom) {
                Ok(atom) => return Ok(atom),
                Err(error) => error,
            };
            self.lx = start.clone();
            Some(error)
        };
        if !self.try_punct("(") {
            return Err(atom_error.expect("lazy alternative starts with a group"));
        }
        let group = self.formula_iff(groups);
        let group = match group {
            Ok(group) => match self.require_punct(")") {
                Ok(()) => Ok(group),
                Err(error) => {
                    if let Some(atom_error) = atom_error {
                        return Err(Self::select_alt_error(error, atom_error));
                    }
                    Err(error)
                }
            },
            Err(error) => Err(error),
        };
        match group {
            Ok(group) if !self.at_term_continuation() => Ok(group),
            Ok(_) => {
                if let Some(error) = atom_error {
                    return Err(error);
                }
                self.lx = start;
                let atom = self.formula_atom();
                self.lx.finish(atom)
            }
            Err(error) => {
                if let Some(atom_error) = atom_error {
                    return Err(Self::select_alt_error(atom_error, error));
                }
                self.lx = start;
                let atom = self.formula_atom();
                self.lx
                    .finish(atom)
                    .map_err(|atom_error| Self::select_alt_error(atom_error, error))
            }
        }
    }
    /// Index each enclosing group once, so choosing the atom alternative for
    /// `(term) = rhs` does not require reparsing every parenthesized suffix.
    /// Strings and comments use the same lexer as the real parser. An
    /// incomplete group takes the original atom-first diagnostic path.
    fn group_is_term(&mut self, groups: &mut tamarin_utils::FastMap<usize, Pos>) -> bool {
        let start = self.save();
        if !groups.contains_key(&start.offset) {
            let mut scan = self.lx.clone();
            let mut openings = Vec::new();
            loop {
                scan.skip_ws();
                match scan.peek() {
                    Some('(') => {
                        openings.push(scan.pos().offset);
                        scan.bump();
                    }
                    Some(')') => {
                        scan.bump();
                        let Some(opening) = openings.pop() else {
                            return true;
                        };
                        groups.insert(opening, scan.pos());
                        if openings.is_empty() {
                            break;
                        }
                    }
                    Some('\'') => {
                        if scan.single_quoted().is_err() {
                            return true;
                        }
                    }
                    Some('"') | None => return true,
                    Some(_) => {
                        scan.bump();
                    }
                }
            }
        }
        let lexer = self.lx.clone();
        self.lx.set_pos(groups[&start.offset]);
        let result = self.at_term_continuation();
        self.lx = lexer;
        result
    }
}

#[cfg(test)]
#[path = "formula_parser_reference.rs"]
mod reference;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn grouped_formula_alternatives_preserve_ast_and_diagnostics() {
        fn parse(source: &str, old: bool) -> String {
            let mut p = Parser::new(source, &[], false);
            p.seed_signature(
                &tamarin_term::maude_sig::hash_maude_sig()
                    .merge(tamarin_term::maude_sig::dh_maude_sig()),
            );
            p.resolve_prefix_apps = false;
            let result = if old {
                p.iterative_formula_reference()
            } else {
                p.formula_body()
            };
            let result = p.lx.finish(result);
            format!("{result:?}")
        }
        let atoms = [
            "T",
            "F",
            "x = y",
            "h(x) = y",
            "P(x)",
            "last(#i)",
            "All x #i. A(x)@i ==> x = x",
            "x",
            "T &",
            "x =",
            "h(x",
            "'a)b' = x",
            "'/*)*/' = x",
            "T /* unclosed",
            "T & F",
            "not T",
            "T ==> F",
            "T <=> F",
        ];
        let mut inputs: Vec<String> = atoms.iter().map(|s| s.to_string()).collect();
        for depth in 1..6 {
            for atom in atoms {
                for prefix in ["", "not ", "T & ", "T ==> "] {
                    for suffix in [
                        "",
                        " = x",
                        " ^ x = y",
                        " & F",
                        ")",
                        "(",
                        " /* trailing",
                        " <=> T",
                    ] {
                        inputs.push(format!(
                            "{prefix}{}{atom}{}{suffix}",
                            "( /*c*/ ".repeat(depth),
                            ")".repeat(depth)
                        ));
                    }
                }
            }
        }
        for source in inputs {
            assert_eq!(parse(&source, false), parse(&source, true), "{source}");
        }
    }
}
