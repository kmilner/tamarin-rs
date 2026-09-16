// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Guarded formula grammar with indexed, lazy ambiguous grouping.
//! Preserves the grammar in Theory/Text/Parser/Formula.hs:61-109.

use super::*;

/// One formula-local record per parenthesis group. Missing closing positions
/// are indexed too. Diagnostic term recognition shares the same records rather
/// than reparsing each enclosing suffix or retaining discarded term ASTs.
#[derive(Default)]
pub(super) struct Groups<'a> {
    entries: tamarin_utils::FastMap<usize, Group<'a>>,
    #[cfg(test)]
    pub steps: usize,
}

#[derive(Default)]
struct Group<'a> {
    boundary: Boundary,
    term: Option<Box<TermOutcome<'a>>>,
}

#[derive(Default)]
enum Boundary {
    #[default]
    Unscanned,
    Unclosed,
    Closed(Pos),
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum GroupKind {
    Term,
    Formula,
    Incomplete,
}

pub(super) struct TermOutcome<'a> {
    pub end: Lexer<'a>,
    pub explicit_sort: bool,
    pub result: Result<Term, ParseError>,
}

impl<'a> Groups<'a> {
    pub(super) fn term(&self, opening: usize) -> Option<&TermOutcome<'a>> {
        self.entries.get(&opening)?.term.as_deref()
    }

    pub(super) fn record_term(&mut self, opening: usize, outcome: TermOutcome<'a>) {
        self.entries.entry(opening).or_default().term = Some(Box::new(outcome));
    }
}

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

impl<'a> Parser<'a> {
    pub(super) fn formula_body(&mut self) -> Result<Formula, ParseError> {
        self.formula_iff(&mut Groups::default())
    }

    fn formula_iff(&mut self, groups: &mut Groups<'a>) -> Result<Formula, ParseError> {
        let left = self.formula_expr(1, groups)?;
        if self.try_punct("<=>") || self.try_punct("⇔") {
            Ok(Binary::Iff.build(left, self.formula_expr(1, groups)?))
        } else {
            Ok(left)
        }
    }

    fn formula_expr(&mut self, min: u8, groups: &mut Groups<'a>) -> Result<Formula, ParseError> {
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

    fn formula_primary(&mut self, groups: &mut Groups<'a>) -> Result<Formula, ParseError> {
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
        let group_kind = self.peek_punct("(").then(|| self.group_kind(groups));
        let lazy = group_kind == Some(GroupKind::Formula);
        let start = self.lx.clone();
        let atom_error = if lazy {
            None
        } else {
            let atom = match group_kind {
                Some(kind) => self.grouped_atom(groups, kind == GroupKind::Incomplete),
                None => self.formula_atom(),
            };
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
                let atom = self.grouped_atom(groups, false);
                self.lx.finish(atom)
            }
            Err(error) => {
                let atom_error = match atom_error {
                    Some(error) => error,
                    None => {
                        self.lx = start;
                        self.grouped_atom(groups, true).unwrap_err()
                    }
                };
                Err(Self::select_alt_error(atom_error, error))
            }
        }
    }
    /// Index each enclosing group once, so choosing the atom alternative for
    /// `(term) = rhs` does not require reparsing every parenthesized suffix.
    /// Strings and comments use the same lexer as the real parser. An
    /// incomplete group is recorded with no closing position; its diagnostic
    /// alternative is recognized on demand through these same group records.
    fn group_kind(&mut self, groups: &mut Groups<'a>) -> GroupKind {
        let start = self.save();
        if groups
            .entries
            .get(&start.offset)
            .is_none_or(|group| matches!(group.boundary, Boundary::Unscanned))
        {
            let mut scan = self.lx.clone();
            let mut openings = Vec::new();
            loop {
                #[cfg(test)]
                {
                    groups.steps += 1;
                }
                scan.skip_ws();
                match scan.peek() {
                    Some('(') => {
                        openings.push(scan.pos().offset);
                        groups
                            .entries
                            .entry(scan.pos().offset)
                            .or_default()
                            .boundary = Boundary::Unclosed;
                        scan.bump();
                    }
                    Some(')') => {
                        scan.bump();
                        let Some(opening) = openings.pop() else {
                            break;
                        };
                        groups.entries.entry(opening).or_default().boundary =
                            Boundary::Closed(scan.pos());
                        if openings.is_empty() {
                            break;
                        }
                    }
                    Some('\'') => {
                        if scan.single_quoted().is_err() {
                            break;
                        }
                    }
                    Some('"') | None => break,
                    Some(_) => {
                        scan.bump();
                    }
                }
            }
        }
        let Boundary::Closed(closing) = groups.entries[&start.offset].boundary else {
            return GroupKind::Incomplete;
        };
        let lexer = self.lx.clone();
        self.lx.set_pos(closing);
        let result = self.at_term_continuation();
        self.lx = lexer;
        if result {
            GroupKind::Term
        } else {
            GroupKind::Formula
        }
    }

    /// A grouped atom starts with a relational term, never a fact. When the
    /// index rules out success, recognition may reuse compact successful group
    /// summaries; otherwise only failed groups are reused and a full AST is built.
    fn grouped_atom(
        &mut self,
        groups: &mut Groups<'a>,
        diagnostic: bool,
    ) -> Result<Formula, ParseError> {
        let start = self.lx.clone();
        let fact_error = self.fact().unwrap_err(); // a fact cannot start with `(`
        let fact_end = self.lx.clone();
        self.lx = start;
        let term = self.grouped_term(groups, diagnostic);
        let relation =
            term.and_then(|lhs| self.relational_atom_after(lhs, self.sort_suffix_consumed));
        let term_error = match self.lx.finish(relation) {
            Ok(formula) => {
                assert!(
                    !diagnostic,
                    "a diagnostic-only group cannot be a valid atom"
                );
                return Ok(formula);
            }
            Err(error) => error,
        };
        self.lx = fact_end;
        self.lx
            .finish(Err(Self::select_alt_error(term_error, fact_error)))
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
        fn parse(source: &str, old: bool, resolve: bool) -> String {
            let mut p = Parser::new(source, &[], false);
            p.seed_signature(
                &tamarin_term::maude_sig::hash_maude_sig()
                    .merge(tamarin_term::maude_sig::dh_maude_sig()),
            );
            p.resolve_prefix_apps = resolve;
            let result = if old {
                p.iff_reference()
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
        // Partial groups and relation-looking suffixes used to trigger repeated
        // atom alternatives. Include failures inside application/list grammars,
        // whose delimiter provenance must not leak into cached inner groups.
        for depth in [1, 2, 8, 32, 64] {
            for atom in [
                "x",
                "x = y",
                "#i",
                "h(x)",
                "h(x,y)",
                "h((x),",
                "<x,(",
                "last(x",
                "T /* unclosed",
                "'unclosed",
                "(",
                "?",
            ] {
                for closed in [0, depth / 2, depth] {
                    for suffix in ["", " = x", " <=> T", " == x", " & F", " /* unfinished"] {
                        inputs.push(format!(
                            "{}{atom}{}{suffix}",
                            "( /*c*/ ".repeat(depth),
                            ")".repeat(closed)
                        ));
                    }
                }
                inputs.push(format!(
                    "{}{atom}{}",
                    "(".repeat(depth),
                    ") = x".repeat(depth)
                ));
            }
        }
        for source in inputs {
            for resolve in [false, true] {
                assert_eq!(
                    parse(&source, false, resolve),
                    parse(&source, true, resolve),
                    "{source}; resolve={resolve}"
                );
            }
        }
    }

    #[test]
    fn malformed_group_work_is_linear_across_nested_alternatives() {
        tamarin_test_support::on_stack(256 * 1024, || {
            for depth in [1024, 4096, 8192] {
                for (middle, closing) in [
                    ("", ""),
                    ("x", ""),
                    ("x", ")"),
                    ("x=x", ")=x"),
                    ("T /* unclosed", ""),
                    ("h(x,", ")"),
                ] {
                    let source = format!("{}{middle}{}", "(".repeat(depth), closing.repeat(depth));
                    let mut parser = Parser::new(&source, &[], false);
                    let mut groups = Groups::default();
                    let result = parser.formula_iff(&mut groups);
                    assert!(parser.lx.finish(result).is_err(), "{middle} / {closing}");
                    assert!(
                        groups.steps < depth * 40,
                        "{} steps at depth {depth}: {middle} / {closing}",
                        groups.steps
                    );
                }
                // Grow the body alongside group depth: cached successful
                // recognition must not retain or repeatedly clone that AST.
                for body in [
                    "T & ".repeat(depth) + "x",
                    "h(".repeat(depth) + "x" + &")".repeat(depth),
                ] {
                    let source = "(".repeat(depth) + &body + &")".repeat(depth);
                    let mut parser = Parser::new(&source, &[], false);
                    parser.resolve_prefix_apps = false;
                    let mut groups = Groups::default();
                    let result = parser.formula_iff(&mut groups);
                    assert!(parser.lx.finish(result).is_err());
                    assert!(
                        groups.steps < depth * 100,
                        "{} steps at depth {depth}",
                        groups.steps
                    );
                }
            }
        });
    }
}
