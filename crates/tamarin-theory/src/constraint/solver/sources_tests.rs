// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;

use crate::test_maude::maude_path;

#[test]
fn default_parameters_match_haskell() {
    let p = IntegerParameters::default();
    assert_eq!(p.open_chains_limit, 10);
    assert_eq!(p.saturation_limit, 5);
    assert!(!p.show_saturation_steps);
}

/// `unsolved_chain_constraints` counts exactly the OPEN `Chain` goals: a
/// solved chain and a non-chain goal are both invisible to it (HS
/// `openChainGoals`, the `-c/--open-chains` budget's input).
#[test]
fn chain_goal_counted() {
    use crate::constraint::constraints::{Goal, NodeId};
    use crate::rule::{ConcIdx, PremIdx};
    use tamarin_term::lterm::{LSort, LVar};
    let mut s = System::empty();
    assert_eq!(unsolved_chain_constraints(&s), 0);
    let n: NodeId = LVar::new("i", LSort::Node, 0);
    s.add_goal(Goal::Chain((n, ConcIdx(0)), (n, PremIdx(0))));
    assert_eq!(unsolved_chain_constraints(&s), 1);
    // A non-chain goal does not count.
    s.add_goal(Goal::Action(
        n,
        crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]),
    ));
    assert_eq!(unsolved_chain_constraints(&s), 1);
    // Neither does a SOLVED chain goal.
    s.goals_mut()[0].1.solved = true;
    assert_eq!(unsolved_chain_constraints(&s), 0);
}

// =========================================================================
// precompute_sources: unique-source caching correctness
// =========================================================================

fn make_rule(name: &str, conc_tag: crate::fact::FactTag) -> crate::theory::OpenProtoRule {
    use crate::fact::Fact;
    use crate::rule::{ProtoRuleE, ProtoRuleEInfo, Rule};
    let conc = Fact::new(conc_tag, vec![]);
    let r: ProtoRuleE = Rule::new(ProtoRuleEInfo::standard(name), vec![], vec![conc], vec![]);
    crate::theory::OpenProtoRule::new(r)
}

/// A `ProofContext` over `rules` with the pair signature.  `None` only when
/// [`maude_path`] resolved nothing (the documented `TAM_ALLOW_NO_MAUDE` skip);
/// a maude that resolved but will not start is the same misconfiguration as a
/// dangling `MAUDE_PATH`, so it panics rather than silently skipping every
/// maude-backed test in this file.
fn ctx_with_rules(
    rules: Vec<crate::theory::OpenProtoRule>,
) -> Option<crate::constraint::solver::context::ProofContext> {
    let h = start_maude(&maude_path()?, tamarin_term::maude_sig::pair_maude_sig());
    Some(crate::constraint::solver::context::ProofContext::new(
        h, rules,
    ))
}

/// See [`ctx_with_rules`] for why a failed start is a panic, not a skip.
fn start_maude(
    path: &str,
    sig: tamarin_term::maude_sig::MaudeSig,
) -> tamarin_term::maude_proc::MaudeHandle {
    tamarin_term::maude_proc::MaudeHandle::start(path, sig).unwrap_or_else(|e| {
        panic!(
            "maude at {path} failed to start: {e:?} — every maude-backed \
             test here would otherwise skip silently"
        )
    })
}

#[test]
fn precompute_sources_picks_single_producer() {
    use crate::fact::{FactTag, Multiplicity};
    let tag = FactTag::Proto(Multiplicity::Linear, "Foo", 0);
    let rules = vec![make_rule("MakeFoo", tag)];
    let ctx = match ctx_with_rules(rules) {
        Some(c) => c,
        None => return,
    };
    // Foo is produced by exactly one rule → unique-source entry.
    let entries: Vec<_> = ctx
        .unique_sources
        .iter()
        .filter(|s| s.fact_tag == tag)
        .collect();
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].rule_name, "MakeFoo");
}

#[test]
fn precompute_sources_drops_multi_producer() {
    use crate::fact::{FactTag, Multiplicity};
    let bar = FactTag::Proto(Multiplicity::Linear, "Bar", 0);
    let foo = FactTag::Proto(Multiplicity::Linear, "Foo", 0);
    let rules = vec![
        make_rule("MakeBarA", bar),
        make_rule("MakeBarB", bar),
        make_rule("MakeFoo", foo),
    ];
    let ctx = match ctx_with_rules(rules) {
        Some(c) => c,
        None => return,
    };
    // Bar is produced by 2 rules → no unique-source entry.
    let entries: Vec<_> = ctx
        .unique_sources
        .iter()
        .filter(|s| s.fact_tag == bar)
        .collect();
    assert!(
        entries.is_empty(),
        "expected no entry for multi-producer tag, got {:?}",
        entries
    );
    // Single-producer Foo in the SAME context, so the emptiness above cannot
    // come from a cache that skipped every rule.
    assert_eq!(
        ctx.unique_sources
            .iter()
            .filter(|s| s.fact_tag == foo)
            .count(),
        1
    );
}

/// `precompute_full_sources` pushes one lazy `Source` per protocol-fact tag,
/// with an uncomputed `cases_cell` materialised on the first `cases(ctx)`
/// call (HS's `initialSource` thunk).  Both halves are pinned here: the
/// per-tag entry exists, and forcing it yields the producing rules' cases.
#[test]
fn precompute_full_sources_emits_per_tag_entries() {
    use crate::fact::{fresh_fact, Fact, FactTag, Multiplicity};
    use crate::rule::{ProtoRuleE, ProtoRuleEInfo, Rule};
    use tamarin_term::builtin::msg_var;

    let path = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = start_maude(&path, tamarin_term::maude_sig::pair_maude_sig());

    let a_tag = FactTag::Proto(Multiplicity::Linear, "A", 1);
    let a_fact = Fact::new(a_tag, vec![msg_var("x", 0)]);
    let init: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Init"),
        vec![fresh_fact(msg_var("x", 0))],
        vec![a_fact.clone()],
        vec![],
    );
    let loop_r: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Loop"),
        vec![a_fact.clone()],
        vec![a_fact.clone()],
        vec![],
    );
    let stop: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Stop"),
        vec![a_fact.clone()],
        vec![],
        vec![],
    );
    let rules = vec![
        crate::theory::OpenProtoRule::new(init),
        crate::theory::OpenProtoRule::new(loop_r),
        crate::theory::OpenProtoRule::new(stop),
    ];
    let ctx = crate::constraint::solver::context::ProofContext::new(h, rules);
    // ctx.full_sources is computed at construction time.
    let a_src = ctx.full_sources.iter().find(|s| match &s.goal {
        crate::constraint::constraints::Goal::Premise(_, fa) => fa.tag == a_tag,
        _ => false,
    });
    assert!(
        a_src.is_some(),
        "expected a precomputed source for tag A; got: {:?}",
        ctx.full_sources.iter().map(|s| &s.goal).collect::<Vec<_>>()
    );
    let a_src = a_src.unwrap();
    // Unforced, the cell is empty — that is what makes the precompute lazy.
    assert!(a_src.cases_or_empty().is_empty());
    // Forcing enumerates the two rules that conclude `A(x)`.
    let names: Vec<String> = a_src.cases(&ctx).into_iter().map(|(n, _)| n).collect();
    assert_eq!(names, ["Init", "Loop"]);
}

/// Bilinear-pairing source, both directions of HS Sources.hs's
/// `if enableBP msig then return $ fAppC EMap $ nMsgVars 2 else []`.
/// Emitting it under a BP signature is what keeps the BP targets
/// (Chen_Kudla, Joux, RYY, Scott, TAK1) from missing the `KU(em(...))`
/// source-case enumeration; NOT emitting it otherwise is what keeps every
/// non-BP theory from growing a spurious extra KU source.
#[test]
fn precompute_full_sources_emits_em_only_when_bp_enabled() {
    use crate::constraint::constraints::Goal;
    use crate::fact::{fresh_fact, Fact, FactTag, Multiplicity};
    use crate::rule::{ProtoRuleE, ProtoRuleEInfo, Rule};
    use tamarin_term::builtin::msg_var;

    let path = match maude_path() {
        Some(p) => p,
        None => return,
    };

    // Minimal protocol so there's at least one proto rule (so
    // `precompute_full_sources` actually runs).
    let a_tag = FactTag::Proto(Multiplicity::Linear, "A", 1);
    let a_fact = Fact::new(a_tag, vec![msg_var("x", 0)]);
    let em_sources = |sig| {
        let init: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("Init"),
            vec![fresh_fact(msg_var("x", 0))],
            vec![a_fact.clone()],
            vec![],
        );
        let rules = vec![crate::theory::OpenProtoRule::new(init)];
        let ctx =
            crate::constraint::solver::context::ProofContext::new(start_maude(&path, sig), rules);
        ctx.full_sources
            .iter()
            .filter(|s| match &s.goal {
                Goal::Action(_, fa) => {
                    fa.tag == FactTag::Ku
                        && fa.terms.len() == 1
                        && matches!(
                            &fa.terms[0],
                            tamarin_term::term::Term::App(
                                tamarin_term::function_symbols::FunSym::C(
                                    tamarin_term::function_symbols::CSym::EMap
                                ),
                                _
                            )
                        )
                }
                _ => false,
            })
            .count()
    };
    assert_eq!(em_sources(tamarin_term::maude_sig::bp_maude_sig()), 1);
    assert_eq!(em_sources(tamarin_term::maude_sig::pair_maude_sig()), 0);
}

#[test]
fn precompute_sources_handles_multiple_unique_tags() {
    use crate::fact::{FactTag, Multiplicity};
    let tag_a = FactTag::Proto(Multiplicity::Linear, "A", 0);
    let tag_b = FactTag::Proto(Multiplicity::Linear, "B", 0);
    let rules = vec![make_rule("MakeA", tag_a), make_rule("MakeB", tag_b)];
    let ctx = match ctx_with_rules(rules) {
        Some(c) => c,
        None => return,
    };
    // Both A and B should appear.
    let names: Vec<_> = ctx
        .unique_sources
        .iter()
        .filter(|s| s.fact_tag == tag_a || s.fact_tag == tag_b)
        .map(|s| &s.rule_name[..])
        .collect();
    assert!(names.contains(&"MakeA"));
    assert!(names.contains(&"MakeB"));
}

// =========================================================================
// Haskell-faithfulness invariants for `restrict_eq_store_to_stable_vars`.
//
// These tests pin the contract: pure key-filter, matching Haskell's
// `Subst.restrict = M.filterWithKey`.
// =========================================================================

/// `restrict_eq_store_to_stable_vars` is a pure key-filter — drops
/// every binding whose KEY is not in stable_vars.  No chain-chase.
///
/// Mirrors `Theory.Tools.EquationStore.restrict`
/// (via `Term.Substitution.Subst.restrict`, SubstVFree.hs:160-161):
/// ```haskell
/// restrict vs (Subst smap) = Subst (M.filterWithKey (\v _ -> v `elem` vs) smap)
/// ```
#[test]
fn restrict_eq_store_keeps_only_stable_keyed_bindings() {
    use std::collections::BTreeSet;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::subst::Subst;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    let t1 = LVar::new("t", LSort::Msg, 1); // stable
    let t2 = LVar::new("t", LSort::Msg, 2); // stable
    let m19 = LVar::new("m", LSort::Msg, 19); // not stable
    let sk28 = LVar::new("sk", LSort::Msg, 28); // not stable

    let pub_a = LVar::new("a", LSort::Pub, 0);
    let pub_b = LVar::new("b", LSort::Pub, 0);
    let mut sys = System::empty();
    sys.invalidate_max_var_idx_cache();
    sys.eq_store_mut().subst = Subst::from_list(vec![
        (t1, Term::Lit(Lit::Var(pub_a))),
        (m19, Term::Lit(Lit::Var(pub_b))),
        (sk28, Term::Lit(Lit::Var(t2))),
    ]);

    let stable: BTreeSet<LVar> = [t1, t2].into_iter().collect();
    restrict_eq_store_to_stable_vars(&mut sys, &stable);

    // t1 binding kept; m19 + sk28 bindings dropped.
    assert!(
        sys.eq_store.subst.image_of(&t1).is_some(),
        "stable-keyed binding (t.1) is kept"
    );
    assert!(
        sys.eq_store.subst.image_of(&m19).is_none(),
        "non-stable-keyed binding (m.19) is dropped"
    );
    assert!(
        sys.eq_store.subst.image_of(&sk28).is_none(),
        "non-stable-keyed binding (sk.28) is dropped, EVEN THOUGH \
                 its VALUE mentions stable t.2 — restrict is key-only."
    );
}

/// `restrict_eq_store_to_stable_vars` does NOT chain-chase.
///
/// This pins the pure key-filter contract.  If someone re-introduces
/// chain-chase here, foo_eligibility-class divergences silently
/// appear in the corpus.
#[test]
fn restrict_eq_store_does_not_chain_chase() {
    use std::collections::BTreeSet;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::subst::Subst;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    // Set up exactly the foo_eligibility shape: a chain
    // t.1 → e.10 → blind_arg.  Stable = {t.1}.  Haskell-faithful:
    // t.1 → e.10 stays (e.10 unbound after filter).  Rust must NOT
    // collapse to t.1 → blind_arg directly.
    let t1 = LVar::new("t", LSort::Msg, 1);
    let e10 = LVar::new("e", LSort::Msg, 10);
    let blind_arg = LVar::new("m", LSort::Msg, 28);

    let mut sys = System::empty();
    sys.invalidate_max_var_idx_cache();
    sys.eq_store_mut().subst = Subst::from_list(vec![
        (t1, Term::Lit(Lit::Var(e10))),
        (e10, Term::Lit(Lit::Var(blind_arg))),
    ]);

    let stable: BTreeSet<LVar> = [t1].into_iter().collect();
    restrict_eq_store_to_stable_vars(&mut sys, &stable);

    // t.1's binding must be exactly e.10 (the var), NOT chain-chased
    // to blind_arg.
    assert_eq!(
        sys.eq_store.subst.image_of(&t1),
        Some(&Term::Lit(Lit::Var(e10))),
        "restrict must NOT chain-chase t.1 → e.10 → blind_arg \
                    into t.1 → blind_arg"
    );
}

/// `restrict_eq_store_to_stable_vars` produces empty subst when no
/// key is stable.  This is the foo_eligibility shape under
/// Haskell-faithful unification orientation: keys are rule-internal
/// vars (large idx), stableVars are lemma vars (small idx).
#[test]
fn restrict_eq_store_empties_subst_when_no_keys_are_stable() {
    use std::collections::BTreeSet;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::subst::Subst;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    let m19 = LVar::new("m", LSort::Msg, 19);
    let sk28 = LVar::new("sk", LSort::Msg, 28);
    let pub_a = LVar::new("a", LSort::Pub, 0);
    let pub_b = LVar::new("b", LSort::Pub, 0);
    let mut sys = System::empty();
    sys.invalidate_max_var_idx_cache();
    sys.eq_store_mut().subst = Subst::from_list(vec![
        (m19, Term::Lit(Lit::Var(pub_a))),
        (sk28, Term::Lit(Lit::Var(pub_b))),
    ]);

    let stable: BTreeSet<LVar> = [LVar::new("t", LSort::Msg, 1), LVar::new("t", LSort::Msg, 2)]
        .into_iter()
        .collect();
    restrict_eq_store_to_stable_vars(&mut sys, &stable);

    assert!(
        sys.eq_store.subst.is_empty(),
        "When no key is in stable set (Haskell shape: keys are \
                 rule-internal large-idx vars, stable are lemma small-idx \
                 vars), restrict produces empty subst.  This is what \
                 enables foo_eligibility's clean runtime applySource bind."
    );
}

// =========================================================================
// HS-faithful source-case naming invariant.
//
// By the time a case name reaches the runtime, `refineSource` has
// already applied HS's `combine` (Sources.hs:135-139, ported in
// `combine_case_names_list`) over the `[String]` step-name list, and
// the result is joined with `intercalate "_"` (ProofMethod.hs:505-515, see line 511).
// The stored name is therefore the FINAL display name and must be
// used verbatim — HS never re-splits a single name on `_`.
// =========================================================================

/// `combine` keeps a single non-coerce element verbatim, including when it
/// is a `c_<sym>` construction-rule name whose symbol contains underscores
/// (e.g. `c_KDF_SKc` must stay intact, never split to `SKc` — the
/// fm24-cardpayments C8 divergence).
#[test]
fn combine_keeps_underscore_bearing_constr_name_intact() {
    // Single construction-rule name → kept whole.
    assert_eq!(
        combine_case_names_list(&["c_KDF_SKc".to_string()], &[]),
        vec!["c_KDF_SKc".to_string()]
    );
    // Leading "coerce" element dropped, next element kept whole.
    assert_eq!(
        combine_case_names_list(&["coerce".to_string(), "c_KDF_SKc".to_string()], &[]),
        vec!["c_KDF_SKc".to_string()]
    );
    // Underscore-free constructors are likewise kept verbatim.
    assert_eq!(
        combine_case_names_list(&["c_senc".to_string()], &[]),
        vec!["c_senc".to_string()]
    );
    // Protocol-rule names with underscores kept whole.
    assert_eq!(
        combine_case_names_list(&["Card_Responds_To_GPO_C8".to_string()], &[]),
        vec!["Card_Responds_To_GPO_C8".to_string()]
    );
}

/// `case_name_list_to_string` is HS `intercalate "_"`.
#[test]
fn case_name_list_to_string_is_intercalate_underscore() {
    assert_eq!(
        case_name_list_to_string(&["c_KDF_SKc".to_string()]),
        "c_KDF_SKc"
    );
    assert_eq!(
        case_name_list_to_string(&["a".to_string(), "b".to_string()]),
        "a_b"
    );
    assert_eq!(case_name_list_to_string(&[]), "");
}
