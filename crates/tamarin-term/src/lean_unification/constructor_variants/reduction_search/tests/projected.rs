use super::*;
use crate::function_symbols::{Constructability, NoEqSym, Privacy};
use crate::term::f_app_no_eq;

fn select(a: LNTerm, b: LNTerm) -> LNTerm {
    f_app_no_eq(symbol(), vec![a, b])
}

fn symbol() -> NoEqSym {
    NoEqSym::new(b"select", 2, Privacy::Public, Constructability::Constructor)
}

fn with_rules(rules: impl IntoIterator<Item = (LNTerm, LNTerm)>) -> MaudeSig {
    let mut sig = signature(rules);
    sig.st_fun_syms.insert(symbol());
    sig.refresh()
}

fn wide() -> LNTerm {
    f_app_ac(
        AcSym::Union,
        (0..64)
            .map(|i| Term::Lit(Lit::Var(LVar::new("f", LSort::Msg, i))))
            .collect(),
    )
}

#[test]
fn projected_rule_reduction_skips_shared_erased_ac_allocations() {
    let (x, y, z, w) = (var("x"), var("y"), var("z"), var("w"));
    let sig = with_rules([(select(bag([x, y, z]), w.clone()), w)]);
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig, AlgebraBackend::NativeOnly).unwrap();
    let frozen = var("x"); // A matching key in the rule, a frozen name in the query.
    assert_eq!(
        native.reduce(&select(wide(), frozen.clone())).unwrap(),
        frozen
    );
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn projected_existence_keeps_connected_patterns_and_rhs_choices() {
    use crate::builtin::emap;
    use crate::maude_sig::bp_maude_sig;
    let (x, y, z, r, s) = (var("x"), var("y"), var("z"), var("r"), var("s"));
    let pattern = select(pair(bag([x.clone(), y, z]), hash(x)), emap(r.clone(), s));
    let sig = with_rules([(pattern, r)]).merge(bp_maude_sig());
    let table = RuleTable::new(&sig).unwrap();
    let (a, b) = (pub_term("a"), pub_term("b"));
    let query = |required| select(pair(wide(), hash(required)), emap(a.clone(), b.clone()));
    let positive = query(Term::Lit(Lit::Var(LVar::new("f", LSort::Msg, 9))));
    assert_eq!(
        table.successors(&positive, &mut 100_000).unwrap(),
        Some([a.clone(), b.clone()].into_iter().collect())
    );
    let miss = query(pub_term("absent"));
    assert_eq!(
        table.successors(&miss, &mut 100_000).unwrap(),
        Some(BTreeSet::new())
    );
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig, AlgebraBackend::NativeOnly).unwrap();
    assert_eq!(native.reduce(&miss).unwrap(), miss);
    // Both choices for the observed commutative operand must reach the graph.
    assert!(matches!(
        native.reduce(&positive),
        Err(crate::maude_proc::MaudeError::UnsupportedOperation(
            "normalization"
        ))
    ));
}

#[test]
fn native_oracle_projected_ground_rhs_preserves_the_ac_subproduct_complement() {
    let marker = NoEqSym::new(b"marker", 0, Privacy::Public, Constructability::Constructor);
    let mark = f_app_no_eq(marker, vec![]);
    let x = var("x");
    let mut sig = with_rules([(bag([x.clone(), x]), mark.clone())]);
    sig.st_fun_syms.insert(marker);
    let sig = sig.refresh();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::NativeOnly)
            .unwrap();
    let (a, b) = (pub_term("a"), pub_term("b"));
    let input = bag([a.clone(), a, b.clone()]);
    let result = bag([mark, b]);
    assert_eq!(native.reduce(&input).unwrap(), result);
    let table = RuleTable::new(&sig).unwrap();
    assert_eq!(table.search_with_budget(&input, 1).unwrap(), None);
    assert_eq!(
        table.successors(&input, &mut 100_000).unwrap(),
        Some([result.clone()].into_iter().collect())
    );
    if std::env::var_os("TAM_RS_VERIFY_LEAN_UNIFY").is_none()
        && let Some(path) = tamarin_test_support::require_maude_path()
    {
        let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
        assert_eq!(oracle.reduce(&input).unwrap(), result);
    }
}

#[test]
fn erased_tree_existence_distinguishes_a_witness_from_exhaustion() {
    use crate::builtin::emap;
    use crate::rewriting::Equal;
    let (a, b) = (pub_term("a"), pub_term("b"));
    let vars = |i| Term::Lit(Lit::Var(LVar::new("value", LSort::Msg, i)));
    let rows: Vec<_> = (0..16)
        .map(|i| Equal {
            lhs: emap(vars(2 * i), vars(2 * i + 1)),
            rhs: emap(a.clone(), b.clone()),
        })
        .collect();
    assert_eq!(
        open_match::has_match_budget(&rows, &mut 5_000).unwrap(),
        Some(true)
    );
    assert_eq!(open_match::has_match_budget(&rows, &mut 1).unwrap(), None);
    assert!(matches!(
        open_match::with_captures_budget(&rows, vec![], &mut 5_000).unwrap(),
        Outcome::Unsupported
    ));
    let conflict = Equal {
        lhs: emap(vars(0), vars(0)),
        rhs: emap(a, b),
    };
    assert_eq!(
        open_match::has_match_budget(&[conflict], &mut 5_000).unwrap(),
        Some(false)
    );
}

#[test]
fn allocation_connected_to_a_returned_key_keeps_its_full_matching_constraints() {
    let (x, y) = (var("x"), var("y"));
    let pattern = select(bag([x.clone(), y]), x.clone());
    let sig = with_rules([(pattern.clone(), x.clone())]);
    let table = RuleTable::new(&sig).unwrap();
    let (a, b) = (pub_term("a"), pub_term("b"));
    let app = |key| select(bag([a.clone(), b.clone()]), key);
    let good = app(a.clone());
    assert!(table
        .projected_rule_values(&pattern, &x, &good, &mut 100_000)
        .unwrap()
        .is_none());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig, AlgebraBackend::NativeOnly).unwrap();
    assert_eq!(native.reduce(&good).unwrap(), a);
    let miss = app(pub_term("missing"));
    assert_eq!(native.reduce(&miss).unwrap(), miss);
}
