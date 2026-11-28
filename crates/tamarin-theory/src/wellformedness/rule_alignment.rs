// Currently GPL 3.0; see README.md for licensing details.
// Derived from Theory/Model/Rule.hs: alignRuleUpToRenaming.

//! Match explicit variants by bijective renaming and ordered inherited actions.
//! Cheap necessary conditions prune action selections before the exact AC match.

use std::collections::{BTreeMap, BTreeSet};
use tamarin_term::function_symbols::FunSym;
use tamarin_term::lterm::{frees, rename_avoiding, LNTerm, LSort, LVar};
use tamarin_term::maude_proc::{MaudeError, MaudeHandle};
use tamarin_term::rewriting::Equal;
use tamarin_term::subst::{apply_vterm, Subst};
use tamarin_term::subst_vfresh::LNSubstVFresh;
use tamarin_term::term::Term;
use tamarin_term::vterm::{var_term, Lit};

use crate::fact::LNFact;
use crate::rule::ProtoRuleE;

type Renaming = BTreeMap<LVar, LVar>;
type Variables = BTreeSet<LVar>;

fn bind(env: &mut Renaming, a: LVar, b: LVar) -> Option<()> {
    if a.sort != b.sort
        || env.get(&a).is_some_and(|v| *v != b)
        || env.get(&b).is_some_and(|v| *v != a)
    {
        return None;
    }
    env.insert(a, b);
    env.insert(b, a);
    Some(())
}

fn counts(vars: &Variables) -> BTreeMap<LSort, usize> {
    let mut result = BTreeMap::new();
    for v in vars {
        *result.entry(v.sort).or_default() += 1;
    }
    result
}

fn skeleton(env: &Renaming, facts: &[LNFact]) -> Vec<LNFact> {
    let subst = Subst::from_list(frees(&facts.to_vec()).into_iter().map(|v| {
        let representative = env
            .get(&v)
            .map_or_else(|| LVar::new("_", v.sort, 0), |w| v.min(*w));
        (v, var_term(representative))
    }));
    facts
        .iter()
        .map(|f| f.map_ref(|t| apply_vterm(&subst, t.clone())))
        .collect()
}

fn force_pairs(env: &mut Renaming, a: &LNTerm, b: &LNTerm) -> Option<()> {
    match (a, b) {
        (Term::Lit(Lit::Var(v)), Term::Lit(Lit::Var(w))) => bind(env, *v, *w)?,
        (Term::App(FunSym::NoEq(_) | FunSym::List, xs), Term::App(_, ys)) => {
            for (x, y) in xs.iter().zip(ys.iter()) {
                force_pairs(env, x, y)?;
            }
        }
        _ => {}
    }
    Some(())
}

struct Alignment<'a> {
    maude: &'a MaudeHandle,
    actual_fixed: Vec<LNFact>,
    expected_fixed: Vec<LNFact>,
    expected: Vec<LNFact>,
    variables: BTreeMap<LNFact, Variables>,
    fact_counts: BTreeMap<LNFact, BTreeMap<LSort, usize>>,
}

impl Alignment<'_> {
    fn match_facts(
        &self,
        env: &Renaming,
        actual: &[LNFact],
        expected: &[LNFact],
    ) -> Option<Renaming> {
        if actual
            .iter()
            .map(|f| &self.fact_counts[f])
            .ne(expected.iter().map(|f| &self.fact_counts[f]))
            || skeleton(env, actual) != skeleton(env, expected)
        {
            return None;
        }
        let mut env = env.clone();
        for (a, b) in actual
            .iter()
            .flat_map(|f| f.terms().iter())
            .zip(expected.iter().flat_map(|f| f.terms().iter()))
        {
            force_pairs(&mut env, a, b)?;
        }
        (skeleton(&env, actual) == skeleton(&env, expected)).then_some(env)
    }

    fn bounds(
        &self,
        mut env: Renaming,
        actions: &[(usize, LNFact)],
        expected: &[LNFact],
    ) -> Option<(Renaming, Vec<(usize, usize)>)> {
        loop {
            if skeleton(&env, &self.actual_fixed) != skeleton(&env, &self.expected_fixed) {
                return None;
            }
            let scan = |reverse: bool| -> Option<Vec<&(usize, LNFact)>> {
                let mut remaining: Box<dyn Iterator<Item = &(usize, LNFact)>> = if reverse {
                    Box::new(actions.iter().rev())
                } else {
                    Box::new(actions.iter())
                };
                let wanted: Box<dyn Iterator<Item = &LNFact>> = if reverse {
                    Box::new(expected.iter().rev())
                } else {
                    Box::new(expected.iter())
                };
                wanted
                    .map(|e| {
                        remaining.find(|(_, a)| {
                            self.match_facts(&env, std::slice::from_ref(a), std::slice::from_ref(e))
                                .is_some()
                        })
                    })
                    .collect()
            };
            let earliest = scan(false)?;
            let mut latest = scan(true)?;
            latest.reverse();
            let mut next = env.clone();
            for ((a, b), e) in earliest.iter().zip(&latest).zip(expected) {
                if a.0 == b.0 {
                    next = self.match_facts(
                        &next,
                        std::slice::from_ref(&a.1),
                        std::slice::from_ref(e),
                    )?;
                }
            }
            if env == next {
                return Some((
                    env,
                    earliest
                        .iter()
                        .zip(latest)
                        .map(|(a, b)| (a.0, b.0))
                        .collect(),
                ));
            }
            env = next;
        }
    }

    fn choices(
        &self,
        env: Renaming,
        actual_vars: Variables,
        expected_vars: Variables,
        actions: &[(usize, LNFact)],
        expected: &[LNFact],
        selected: &mut Vec<LNFact>,
    ) -> Result<Option<Vec<LNFact>>, MaudeError> {
        let Some((env, bounds)) = self.bounds(env, actions, expected) else {
            return Ok(None);
        };
        self.bounded_choices(
            env,
            actual_vars,
            expected_vars,
            actions,
            expected,
            &bounds,
            selected,
        )
    }

    fn bounded_choices(
        &self,
        env: Renaming,
        actual_vars: Variables,
        mut expected_vars: Variables,
        actions: &[(usize, LNFact)],
        expected: &[LNFact],
        bounds: &[(usize, usize)],
        selected: &mut Vec<LNFact>,
    ) -> Result<Option<Vec<LNFact>>, MaudeError> {
        let Some(e) = expected.first() else {
            let actual: Vec<_> = self
                .actual_fixed
                .iter()
                .chain(selected.iter())
                .cloned()
                .collect();
            let equations = actual
                .iter()
                .flat_map(|f| f.terms().iter())
                .zip(self.expected.iter().flat_map(|f| f.terms().iter()))
                .map(|(a, b)| Equal::new(a.clone(), b.clone()))
                .collect::<Vec<_>>();
            let actual_vars = frees(&actual);
            let expected_vars = frees(&self.expected);
            let matches = self.maude.unify(&equations)?.into_iter().any(|bindings| {
                let subst = LNSubstVFresh::from_list(bindings);
                subst.restrict(&actual_vars).is_renaming()
                    && subst.restrict(&expected_vars).is_renaming()
            });
            return Ok(matches.then(|| selected.clone()));
        };
        expected_vars.extend(&self.variables[e]);
        let expected_counts = counts(&expected_vars);
        let (lo, hi) = bounds[0];
        let mut seen = BTreeSet::new();
        for (offset, (i, a)) in actions.iter().enumerate() {
            if *i < lo {
                continue;
            }
            if *i > hi {
                break;
            }
            if !seen.insert(a) {
                continue;
            }
            let mut variables = actual_vars.clone();
            variables.extend(&self.variables[a]);
            if counts(&variables) != expected_counts {
                continue;
            }
            let Some(next) =
                self.match_facts(&env, std::slice::from_ref(a), std::slice::from_ref(e))
            else {
                continue;
            };
            selected.push(a.clone());
            let result = if *i == lo && next == env {
                self.bounded_choices(
                    next,
                    variables,
                    expected_vars.clone(),
                    &actions[offset + 1..],
                    &expected[1..],
                    &bounds[1..],
                    selected,
                )
            } else {
                self.choices(
                    next,
                    variables,
                    expected_vars.clone(),
                    &actions[offset + 1..],
                    &expected[1..],
                    selected,
                )
            };
            selected.pop();
            let result = result?;
            if result.is_some() {
                return Ok(result);
            }
        }
        Ok(None)
    }
}

pub(super) fn align_rule(
    maude: &MaudeHandle,
    member: &ProtoRuleE,
    computed: &ProtoRuleE,
) -> Result<Option<Vec<LNFact>>, MaudeError> {
    if member.info.name != computed.info.name
        || member.premises.len() != computed.premises.len()
        || member.conclusions.len() != computed.conclusions.len()
    {
        return Ok(None);
    }
    let actual_fixed: Vec<_> = member
        .premises
        .iter()
        .chain(&member.conclusions)
        .cloned()
        .collect();
    let expected_fixed: Vec<_> = computed
        .premises
        .iter()
        .chain(&computed.conclusions)
        .cloned()
        .collect();
    let mut remaining = member.actions.iter();
    if actual_fixed == expected_fixed && computed.actions.iter().all(|e| remaining.any(|a| a == e))
    {
        return Ok(Some(computed.actions.clone()));
    }
    let avoid: Vec<_> = actual_fixed
        .iter()
        .chain(&member.actions)
        .cloned()
        .collect();
    let expected = rename_avoiding(
        expected_fixed
            .into_iter()
            .chain(computed.actions.iter().cloned())
            .collect::<Vec<_>>(),
        &avoid,
    );
    let (fixed, actions) = expected.split_at(actual_fixed.len());
    let variables: BTreeMap<_, Variables> = avoid
        .iter()
        .chain(&expected)
        .map(|f| (f.clone(), frees(f).into_iter().collect()))
        .collect();
    let alignment = Alignment {
        maude,
        actual_fixed,
        expected_fixed: fixed.to_vec(),
        fact_counts: variables
            .iter()
            .map(|(f, vs)| (f.clone(), counts(vs)))
            .collect(),
        variables,
        expected: expected.clone(),
    };
    let Some(env) = alignment.match_facts(&Renaming::new(), &alignment.actual_fixed, fixed) else {
        return Ok(None);
    };
    alignment.choices(
        env,
        frees(&alignment.actual_fixed).into_iter().collect(),
        frees(&fixed.to_vec()).into_iter().collect(),
        &member
            .actions
            .iter()
            .cloned()
            .enumerate()
            .collect::<Vec<_>>(),
        actions,
        &mut Vec::new(),
    )
}
