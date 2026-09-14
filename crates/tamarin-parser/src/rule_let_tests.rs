//! Capture-avoiding substitution checked against the previous subtree algorithm.
use super::*;

fn var(name: &str, idx: u64) -> VarSpec {
    VarSpec {
        name: name.into(),
        idx,
        sort: LSort::Msg,
        typ: None,
    }
}

// Compare binding structure, free identities and annotations independently of
// the fresh-name policy. This small-input oracle deliberately uses recursion.
fn canonical(mut formula: Formula) -> Formula {
    fn go(
        formula: &mut Formula,
        env: &tamarin_utils::FastMap<(String, LSort, u64), u64>,
        next: &mut u64,
    ) {
        match formula {
            Formula::Atom(atom) => visit_atom_terms_mut(atom, |term| {
                term.visit_mut(|term| {
                    if let Term::Var(v) = term
                        && let Some(index) = env.get(&rule_var_key(v))
                    {
                        v.name = "\0bound".into();
                        v.idx = *index;
                    }
                    true
                });
            }),
            Formula::Forall(vars, body) | Formula::Exists(vars, body) => {
                let mut env = env.clone();
                for v in vars {
                    env.insert(rule_var_key(v), *next);
                    v.name = "\0bound".into();
                    v.idx = *next;
                    *next += 1;
                }
                go(body, &env, next);
            }
            Formula::Not(body) => go(body, env, next),
            Formula::And(a, b)
            | Formula::Or(a, b)
            | Formula::Implies(a, b)
            | Formula::Iff(a, b) => {
                go(a, env, next);
                go(b, env, next);
            }
            _ => {}
        }
    }
    go(&mut formula, &tamarin_utils::FastMap::default(), &mut 0);
    formula
}

#[test]
fn scoped_substitution_matches_previous_binding_semantics() {
    fn roll(seed: &mut u64) -> usize {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (*seed >> 32) as usize
    }
    fn variable(seed: &mut u64) -> VarSpec {
        let n = roll(seed);
        let mut v = var(["x", "y", "z"][n % 3], [0, 1, 2, u64::MAX][n / 3 % 4]);
        if n.is_multiple_of(5) {
            v.sort = LSort::Nat;
        }
        if n.is_multiple_of(7) {
            v.typ = Some("payload".into());
        }
        v
    }
    fn tree(seed: &mut u64, depth: usize) -> Formula {
        if depth == 0 {
            let a = Term::Var(variable(seed));
            let b = Term::Pair(vec![Term::Var(variable(seed)), Term::Var(variable(seed))]);
            let fact = Fact {
                persistent: false,
                name: "P".into(),
                args: vec![a.clone(), b.clone()],
                annotations: vec![],
            };
            return Formula::Atom(match roll(seed) % 8 {
                0 => Atom::Eq(a, b),
                1 => Atom::Less(a, b),
                2 => Atom::LessMset(a, b),
                3 => Atom::Subterm(a, b),
                4 => Atom::Action(fact, a),
                5 => Atom::Last(a),
                _ => Atom::Pred(fact),
            });
        }
        match roll(seed) % 8 {
            0 => Formula::Not(Box::new(tree(seed, depth - 1))),
            1 => Formula::And(
                Box::new(tree(seed, depth - 1)),
                Box::new(tree(seed, depth - 1)),
            ),
            2 => Formula::Or(
                Box::new(tree(seed, depth - 1)),
                Box::new(tree(seed, depth - 1)),
            ),
            3 => Formula::Implies(
                Box::new(tree(seed, depth - 1)),
                Box::new(tree(seed, depth - 1)),
            ),
            4 => Formula::Iff(
                Box::new(tree(seed, depth - 1)),
                Box::new(tree(seed, depth - 1)),
            ),
            n => {
                let vars = (0..roll(seed) % 5).map(|_| variable(seed)).collect();
                let body = Box::new(tree(seed, depth - 1));
                if n == 5 {
                    Formula::Forall(vars, body)
                } else {
                    Formula::Exists(vars, body)
                }
            }
        }
    }
    for seed in 0..4000 {
        let mut seed = seed;
        let mut actual = tree(&mut seed, 4);
        let mut expected = actual.clone();
        // Sequential substitutions also exercise generated names being seen by
        // later bindings, and RHSs containing their own substitution domain.
        for _ in 0..3 {
            let key = variable(&mut seed);
            let value = Term::Pair((0..4).map(|_| Term::Var(variable(&mut seed))).collect());
            subst_let_formula(&mut actual, &key, &value, &std::cell::OnceCell::new());
            reference(&mut expected, &key, &value, &std::cell::OnceCell::new());
            assert_eq!(canonical(actual.clone()), canonical(expected.clone()));
        }
    }
}

#[test]
fn shadowing_the_domain_still_applies_outer_renames_and_restores_sibling_scopes() {
    for source in [
        "Ex y. (x = y & (All x. x = y))",
        "(Ex y. x = y) & x = y",
        "Ex y. ((All y. x = y) & x = y)",
        "Ex y y. x = y",
    ] {
        let mut actual = Parser::new(source, &[], false).formula().unwrap();
        let mut expected = actual.clone();
        let key = var("x", 0);
        let value = Term::Pair(vec![Term::Var(key.clone()), Term::Var(var("y", 0))]);
        subst_let_formula(&mut actual, &key, &value, &std::cell::OnceCell::new());
        reference(&mut expected, &key, &value, &std::cell::OnceCell::new());
        assert_eq!(canonical(actual), canonical(expected), "{source}");
    }
}

#[test]
fn freshening_combines_wide_binders_large_bodies_and_deep_scopes() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let n = 8192;
        let key = var("x", 0);
        let vars: Vec<_> = (0..n).map(|i| var("y", i)).collect();
        let replacement = Term::Pair(vars.iter().cloned().map(Term::Var).collect());
        let mut body = Formula::Atom(Atom::Eq(
            Term::Var(key.clone()),
            Term::Pair(vars.iter().cloned().map(Term::Var).collect()),
        ));
        for i in 0..n {
            // Many nested conflicts around a large body: no subtree rescans.
            body = Formula::Exists(vec![var("y", i)], Box::new(body));
        }
        let mut formula = Formula::Forall(vars, Box::new(body));
        subst_let_formula(
            &mut formula,
            &key,
            &replacement,
            &std::cell::OnceCell::new(),
        );
        let mut indices = tamarin_utils::FastSet::default();
        let mut atoms = 0;
        formula.visit(|node| match node {
            Formula::Forall(vars, _) | Formula::Exists(vars, _) => {
                for v in vars {
                    assert!(v.idx >= n);
                    assert!(indices.insert(v.idx));
                }
            }
            Formula::Atom(Atom::Eq(a, b)) => {
                atoms += 1;
                assert_eq!(a, &replacement);
                let Term::Pair(bound) = b else {
                    panic!("expected bound variables")
                };
                for t in bound {
                    let Term::Var(v) = t else {
                        panic!("expected variable")
                    };
                    assert!(v.idx >= n * 2);
                }
            }
            _ => {}
        });
        assert_eq!(atoms, 1);
        assert_eq!(indices.len(), n as usize * 2);
    });
}

fn reference(
    phi: &mut Formula,
    key: &VarSpec,
    val: &Term,
    replacement_vars: &std::cell::OnceCell<RuleVars>,
) {
    phi.visit_mut(|phi| {
        match phi {
            Formula::Atom(a) => subst_let_atom(a, key, val),
            Formula::Forall(vars, body) | Formula::Exists(vars, body) => {
                // A rule-let substitution is a free-variable substitution. A
                // quantifier for its domain shadows every occurrence below it.
                if vars.iter().any(|v| same_rule_var(v, key)) {
                    return false;
                }
                let replacement_vars = replacement_vars.get_or_init(|| {
                    let mut vars = RuleVars::default();
                    collect_term_vars(val, &mut vars);
                    vars
                });

                // Parser formulas still carry named variables. Alpha-rename any
                // binder that occurs free in the replacement before descending,
                // otherwise `let x = y in Ex y. ...x...` captures the inserted y.
                if !vars
                    .iter()
                    .any(|var| replacement_vars.contains(&rule_var_key(var)))
                {
                    return true;
                }
                let mut used_vars = replacement_vars.clone();
                collect_formula_vars(body, &mut used_vars);
                for var in vars.iter() {
                    used_vars.insert(rule_var_key(var));
                }
                used_vars.insert(rule_var_key(key));
                for var in vars.iter_mut() {
                    if replacement_vars.contains(&rule_var_key(var)) {
                        let old = var.clone();
                        let fresh = fresh_formula_var(&used_vars, &old);
                        rename_bound_formula(body, &old, &fresh);
                        used_vars.insert(rule_var_key(&fresh));
                        *var = fresh;
                    }
                }
            }
            _ => {}
        }
        true
    });
}

fn fresh_formula_var(used: &RuleVars, old: &VarSpec) -> VarSpec {
    let mut fresh = old.clone();
    // Search from zero so an existing u64::MAX index cannot pin the search.
    // A finite in-memory list cannot occupy every u64 index.
    fresh.idx = 0;
    while used.contains(&rule_var_key(&fresh)) {
        fresh.idx += 1;
    }
    fresh
}

/// Rename occurrences bound by the current quantifier. A nested quantifier
/// for the same variable starts a new scope and stops the traversal there.
fn rename_bound_formula(formula: &mut Formula, old: &VarSpec, new: &VarSpec) {
    formula.visit_mut(|formula| {
        match formula {
            Formula::Atom(atom) => rename_atom_var(atom, old, new),
            Formula::Forall(vars, _) | Formula::Exists(vars, _) => {
                return !vars.iter().any(|v| same_rule_var(v, old));
            }
            _ => {}
        }
        true
    });
}

fn rename_atom_var(atom: &mut Atom, old: &VarSpec, new: &VarSpec) {
    match atom {
        Atom::Eq(a, b) | Atom::Less(a, b) | Atom::LessMset(a, b) | Atom::Subterm(a, b) => {
            rename_term_var(a, old, new);
            rename_term_var(b, old, new);
        }
        Atom::Action(fact, node) => {
            for arg in &mut fact.args {
                rename_term_var(arg, old, new);
            }
            rename_term_var(node, old, new);
        }
        Atom::Last(node) => rename_term_var(node, old, new),
        Atom::Pred(fact) => {
            for arg in &mut fact.args {
                rename_term_var(arg, old, new);
            }
        }
    }
}

fn rename_term_var(term: &mut Term, old: &VarSpec, new: &VarSpec) {
    term.visit_mut(|term| {
        if let Term::Var(v) = term
            && same_rule_var(v, old)
        {
            v.idx = new.idx;
        }
        true
    });
}
