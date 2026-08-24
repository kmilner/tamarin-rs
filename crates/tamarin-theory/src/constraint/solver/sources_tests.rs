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

/// `unsolved_chain_constraints` counts exactly the open `Chain` goals.  It
/// does not see a solved chain, and it does not see a non-chain goal.  This
/// matches HS `openChainGoals`, which is the input of the `-c/--open-chains`
/// budget.
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
    // A solved chain goal does not count either.
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

/// A `ProofContext` over `rules` with the pair signature.  The result is
/// `None` only when [`maude_path`] resolves nothing.  That case is the
/// documented `TAM_ALLOW_NO_MAUDE` skip.  A maude that resolves but does not
/// start is the same misconfiguration as a dangling `MAUDE_PATH`.  This
/// function therefore panics.  A skip would leave every maude-backed test in
/// this file unrun, and no message would report that.
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
    // Foo has a single producer in the same context.  So the empty result
    // above cannot come from a cache that skipped every rule.
    assert_eq!(
        ctx.unique_sources
            .iter()
            .filter(|s| s.fact_tag == foo)
            .count(),
        1
    );
}

/// `precompute_full_sources` pushes one lazy `Source` for each protocol-fact
/// tag.  Each `Source` holds an uncomputed `cases_cell`.  The first
/// `cases(ctx)` call computes that cell.  This is HS's `initialSource` thunk.
/// The test pins both halves.  The per-tag entry exists, and a forced cell
/// gives the cases of the producing rules.
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
    // The cell is empty while nothing forces it.  That is what makes the
    // precompute lazy.
    assert!(a_src.cases_or_empty().is_empty());
    // A forced cell lists the two rules that conclude `A(x)`.
    let names: Vec<String> = a_src.cases(&ctx).into_iter().map(|(n, _)| n).collect();
    assert_eq!(names, ["Init", "Loop"]);
}

/// The bilinear-pairing source.  The test covers both directions of this
/// expression in HS Sources.hs:
/// `if enableBP msig then return $ fAppC EMap $ nMsgVars 2 else []`.
/// A BP signature must emit this source.  Without it, the BP targets
/// (Chen_Kudla, Joux, RYY, Scott, TAK1) miss the `KU(em(...))` source-case
/// enumeration.  Any other signature must not emit it.  Such an emission
/// would give every non-BP theory one extra KU source that does not belong
/// there.
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

    restrict_eq_store_to_stable_vars(&mut sys, &[t1, t2]);

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

    restrict_eq_store_to_stable_vars(&mut sys, &[t1]);

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

    restrict_eq_store_to_stable_vars(
        &mut sys,
        &[LVar::new("t", LSort::Msg, 1), LVar::new("t", LSort::Msg, 2)],
    );

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

/// The system key spells the sort of every quantifier binder, so the five
/// sorts have to key apart: two systems whose binders differ only in sort are
/// distinct and must not be deduplicated against each other.
#[test]
fn binder_sorts_key_apart() {
    use std::collections::BTreeSet;
    use tamarin_term::lterm::LSort;
    let key = |s: &LSort| {
        let mut out = String::new();
        push_sort_dbg(&mut out, *s);
        out
    };
    let sorts = [
        LSort::Pub,
        LSort::Fresh,
        LSort::Msg,
        LSort::Node,
        LSort::Nat,
    ];
    let keys: BTreeSet<String> = sorts.iter().map(key).collect();
    assert_eq!(keys.len(), sorts.len());
}

// =========================================================================
// rename_system_by
// =========================================================================

use crate::constraint::constraints::{Disj, Edge, Goal, LessAtom, NodeId, Reason, SplitId};
use crate::constraint::system::GoalStatus;
use crate::fact::{FactTag, LNFact};
use crate::guarded::Guarded;
use crate::rule::{ConcIdx, IntrRuleACInfo, PremIdx, Rule, RuleACInst, RuleInfo};
use crate::tools::equation_store::EqDisj;
use crate::tools::subterm_store::{SortedPairSet, SubtermConstraint};
use std::sync::Arc;
use tamarin_term::function_symbols::AcSym;
use tamarin_term::lterm::{frees_list, HasFrees, LNTerm, LSort, LVar};
use tamarin_term::subst::Subst;
use tamarin_term::subst_vfresh::SubstVFresh;
use tamarin_term::term::Term;
use tamarin_term::vterm::Lit;

fn nvar(idx: u64) -> NodeId {
    LVar::new("i", LSort::Node, idx)
}

fn mvar(idx: u64) -> LVar {
    LVar::new("x", LSort::Msg, idx)
}

fn mterm(idx: u64) -> LNTerm {
    Term::Lit(Lit::Var(mvar(idx)))
}

/// A rule instance whose single premise holds `t`.
fn rule_holding(t: LNTerm) -> RuleACInst {
    Rule::new(
        RuleInfo::Intr(IntrRuleACInfo::Coerce),
        vec![LNFact::new(FactTag::Out, vec![t])],
        Vec::new(),
        Vec::new(),
    )
}

fn subterm_constraint(small: u64, big: u64) -> SubtermConstraint {
    SubtermConstraint {
        small: mterm(small),
        big: mterm(big),
        propagated: true,
    }
}

/// A `last(i.idx)` formula over one free node leaf.
fn last_formula(idx: u64) -> Guarded {
    use tamarin_parser::ast::{Atom, Term as PTerm, VarSpec};
    Guarded::Atom(crate::guarded::atom_to_gatom_free(&Atom::Last(PTerm::Var(
        VarSpec {
            name: "i".to_string(),
            idx,
            sort: LSort::Node,
            typ: None,
        },
    ))))
}

/// A system carrying a distinct variable in every field the `HasFrees`
/// instance walks, plus the two the instance carries over untouched
/// (`old_neg_subterms` and the ranges of the equation store's disjunctions).
/// The node rule of `nodes[0]` holds `t`, so a caller can plant a term whose
/// shape it wants to read back.
fn system_with_a_variable_per_field(t: LNTerm) -> System {
    let mut s = System::empty();
    s.content_mut().nodes = Arc::new(vec![(nvar(10), rule_holding(t))]);
    s.content_mut().edges = vec![Edge {
        src: (nvar(30), ConcIdx(0)),
        tgt: (nvar(31), PremIdx(0)),
    }];
    s.content_mut().less_atoms = vec![LessAtom::new(nvar(40), nvar(41), Reason::Fresh)];
    s.content_mut().last_atom = Some(nvar(50));
    {
        let st = s.subterm_store_mut();
        st.neg_subterms = SortedPairSet::rebuild_from(vec![(mterm(90), mterm(91))]);
        st.old_neg_subterms = SortedPairSet::rebuild_from(vec![(mterm(98), mterm(99))]);
        st.subterms = vec![subterm_constraint(70, 71)];
        st.solved_subterms = vec![subterm_constraint(80, 81)];
    }
    {
        let es = s.eq_store_mut();
        es.subst = Subst::from_list(vec![(mvar(100), mterm(101))]);
        es.conj = vec![EqDisj {
            split_id: SplitId(0),
            substs: vec![SubstVFresh::from_list(vec![(mvar(110), mterm(111))])],
        }];
    }
    s.content_mut().formulas = vec![Arc::new(last_formula(120))];
    s.content_mut().solved_formulas = vec![Arc::new(last_formula(130))];
    s.content_mut().lemmas = vec![Arc::new(last_formula(140))];
    s.content_mut().goals = Arc::new(vec![
        (
            Goal::Action(nvar(150), LNFact::new(FactTag::Out, vec![mterm(151)])),
            GoalStatus::default(),
        ),
        (
            Goal::Disj(Disj::new(vec![last_formula(170)])),
            GoalStatus::default(),
        ),
        (
            Goal::Subterm((mterm(180), mterm(181))),
            GoalStatus::default(),
        ),
    ]);
    s
}

/// `rename th0` moves every free variable of the system by the shift, which
/// is `mapFrees (Monotone (incVar shift))` over all thirteen fields of the
/// Haskell record (LTerm.hs:643, System.hs:1864-1877) — the negative subterms
/// included.  The two values the instance carries over stay put: the ranges
/// of the equation store's disjunctions, whose variables count as fresh
/// (SubstVFresh.hs:196-202), and `old_neg_subterms` (SubtermStore.hs:95).
#[test]
fn rename_system_by_shifts_every_field_including_neg_subterms() {
    let sys = system_with_a_variable_per_field(mterm(11));
    let out = rename_system_by(&sys, 1000);

    let expected: Vec<LVar> = frees_list(&sys)
        .into_iter()
        .map(|v| LVar::new(v.name, v.sort, v.idx + 1000))
        .collect();
    assert_eq!(frees_list(&out), expected);

    assert_eq!(
        out.subterm_store.neg_subterms.to_vec(),
        vec![(mterm(1090), mterm(1091))],
        "the negative subterms move with the rest of the store"
    );
    assert_eq!(
        out.eq_store.conj[0].substs[0].to_list(),
        vec![(mvar(1110), mterm(111))],
        "a disjunction's domain key moves and its range does not"
    );
    assert_eq!(
        out.subterm_store.old_neg_subterms.to_vec(),
        vec![(mterm(98), mterm(99))]
    );
}

/// The shift is a `Monotone` map (LTerm.hs:643), so it rebuilds an AC
/// argument list with `unsafefApp` and keeps its order.  That is sound
/// because `Ord LVar` compares the index first (LTerm.hs:546-548): adding one
/// constant to every index cannot reorder two arguments, so the result is in
/// AC-normal form already and equals what the re-sorting `Arbitrary` map
/// produces.
#[test]
fn shift_keeps_ac_arg_order() {
    // `z.1` before `a.2` in AC-normal form: the index decides, not the name.
    let low = Term::Lit(Lit::Var(LVar::new("z", LSort::Msg, 1)));
    let high = Term::Lit(Lit::Var(LVar::new("a", LSort::Msg, 2)));
    let product = tamarin_term::term::f_app_ac(AcSym::Mult, vec![low, high]);
    let sys = system_with_a_variable_per_field(product);

    let out = rename_system_by(&sys, 1000);
    let args = match &out.nodes[0].1.premises[0].terms[0] {
        Term::App(_, args) => args.to_vec(),
        _ => unreachable!("the fixture stores an AC application"),
    };
    assert_eq!(
        args,
        vec![
            Term::Lit(Lit::Var(LVar::new("z", LSort::Msg, 1001))),
            Term::Lit(Lit::Var(LVar::new("a", LSort::Msg, 1002))),
        ]
    );
    assert_eq!(
        out,
        sys.map_free(&mut |v: LVar| LVar::new(v.name, v.sort, v.idx + 1000)),
        "the monotone shift and the re-sorting one agree"
    );
}

// =========================================================================
// rename_system_above
// =========================================================================

/// The saturate-time shift is `rename` over `instance HasFrees System`
/// (System.hs:1864-1877), so the goal store's disjunctions and subterm pairs
/// move with everything else (Constraints.hs:226-232) and so do the subterm
/// store's negative subterms (SubtermStore.hs:552-557).  The ranges of the
/// equation store's disjunctions stay put: their variables count as fresh, so
/// the instance maps the domain only (SubstVFresh.hs:196-202).
#[test]
fn saturate_shift_moves_disj_and_subterm_goals_and_leaves_conj_ranges() {
    let sys = system_with_a_variable_per_field(mterm(11));
    let out = rename_system_above(&sys, 999);

    let expected: Vec<LVar> = frees_list(&sys)
        .into_iter()
        .map(|v| LVar::new(v.name, v.sort, v.idx + 1000))
        .collect();
    assert_eq!(frees_list(&out), expected);

    assert_eq!(
        out.goals[1].0,
        Goal::Disj(Disj::new(vec![last_formula(1170)])),
        "a disjunction goal's formula moves with the system"
    );
    assert_eq!(
        out.goals[2].0,
        Goal::Subterm((mterm(1180), mterm(1181))),
        "a subterm goal's pair moves with the system"
    );
    assert_eq!(
        out.subterm_store.neg_subterms.to_vec(),
        vec![(mterm(1090), mterm(1091))],
        "the negative subterms move with the rest of the store"
    );
    assert_eq!(
        out.eq_store.conj[0].substs[0].to_list(),
        vec![(mvar(1110), mterm(111))],
        "a disjunction's domain key moves and its range does not"
    );
}

/// The map invalidates the node-component cache, and the wrapper re-establishes
/// it from the pre-shift value: every node variable's index rises by the same
/// shift, so the maximum over them does too.
#[test]
fn saturate_shift_carries_the_node_component_cache() {
    use crate::constraint::solver::reduction::{bounds_max, bounds_max_uncached};
    let sys = system_with_a_variable_per_field(mterm(11));
    bounds_max(&sys);
    let before = sys
        .node_max_cache
        .get()
        .expect("bounds_max populates the node component");

    let out = rename_system_above(&sys, 999);
    assert_eq!(out.node_max_cache.get(), Some(before + 1000));
    assert_eq!(bounds_max(&out), bounds_max_uncached(&out));
}

// =========================================================================
// some_inst_system
// =========================================================================

/// `evalBindT (someInst sysTh0) keepVarBindings` (Sources.hs:342-348) draws
/// one identifier per free variable it has not already bound, in the order
/// `instance HasFrees System` (System.hs:1832-1877) reaches them: the nodes,
/// the edges, the less atoms, the last atom, the subterm store — negative
/// subterms first (SubtermStore.hs:546-557) — the equation store's
/// substitution and then its disjunctions' domain keys
/// (SubstVFresh.hs:196-202), the three formula stores and the goals.  A
/// variable the store already binds to itself is returned unchanged and
/// charged nothing (Control/Monad/Bind.hs:134-140).
#[test]
fn some_inst_system_keeps_the_seeded_vars_and_draws_in_hs_field_order() {
    let path = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let maude = start_maude(&path, tamarin_term::maude_sig::pair_maude_sig());
    let sys = system_with_a_variable_per_field(mterm(11));
    // The goal's own variables: the node the case is grafted onto and the
    // term of its fact, in the ascending order `frees` hands over.
    let keep = [nvar(10), mvar(11)];

    maude.reset_counter_to(500);
    let out = some_inst_system(&sys, &keep, &maude);

    let node = |idx: u64| nvar(idx);
    let msg = |idx: u64| mvar(idx);
    assert_eq!(
        frees_list(&out),
        vec![
            // sNodes: the node id and the term of its rule's premise, both
            // seeded, so the walk opens without a draw.
            node(10),
            msg(11),
            // sEdges, sLessAtoms, sLastAtom.
            node(500),
            node(501),
            node(502),
            node(503),
            node(504),
            // sSubtermStore: the negative pair, then the positive one, then
            // the solved one.
            msg(505),
            msg(506),
            msg(507),
            msg(508),
            msg(509),
            msg(510),
            // sEqStore: the substitution's key and value, then the
            // disjunction's domain key.
            msg(511),
            msg(512),
            msg(513),
            // sFormulas, sSolvedFormulas, sLemmas.
            node(514),
            node(515),
            node(516),
            // sGoals in ascending `Ord Goal`: the action goal's node and
            // fact, the disjunction, the subterm pair.
            node(517),
            msg(518),
            node(519),
            msg(520),
            msg(521),
        ]
    );
    assert_eq!(
        maude.fresh_counter_peek(),
        522,
        "one identifier per variable that is not seeded"
    );
    assert_eq!(
        out.subterm_store.neg_subterms.to_vec(),
        vec![(mterm(505), mterm(506))],
        "the negative subterms are imported before the positive ones"
    );
    assert_eq!(
        out.eq_store.conj[0].substs[0].to_list(),
        vec![(mvar(513), mterm(111))],
        "a disjunction's domain key is imported and its range is not"
    );
    assert_eq!(
        out.subterm_store.old_neg_subterms.to_vec(),
        vec![(mterm(98), mterm(99))]
    );
}

// =========================================================================
// compute_rename_map
// =========================================================================

/// `renameDropNameHints` (Sources.hs:252-258) imports the system's variables
/// in the order `instance HasFrees System` (System.hs:1832-1848) reaches
/// them, which for a disjunction of the equation store is ascending
/// `Ord LNSubstVFresh` — HS holds it as an `S.Set` (EquationStore.hs:116-121)
/// and the set instance folds `S.toList` (LTerm.hs:898-901).  The port stores
/// the disjunction as an insertion-ordered `Vec`, so a walk reading that
/// `Vec` would hand the two substitutions' domain keys the opposite pair of
/// indices, and two systems that differ only in insertion order would take
/// different dedup keys.
#[test]
fn rename_map_walks_inner_conj_substs_in_ord_order() {
    let mut sys = System::empty();
    {
        let es = sys.eq_store_mut();
        es.conj = vec![EqDisj {
            split_id: SplitId(0),
            substs: vec![
                SubstVFresh::from_list(vec![(mvar(2), mterm(3))]),
                SubstVFresh::from_list(vec![(mvar(1), mterm(4))]),
            ],
        }];
    }
    let rename = compute_rename_map(&sys, &std::collections::BTreeSet::new());
    assert_eq!(rename.get(&mvar(1)), Some(LVar::new("", LSort::Msg, 0)));
    assert_eq!(rename.get(&mvar(2)), Some(LVar::new("", LSort::Msg, 1)));
}

/// The subterm store folds its negative subterms before its positive and
/// solved ones (SubtermStore.hs:546-549), so a variable that occurs in a
/// negative subterm alone is imported like any other and the dedup key
/// carries its renamed identity.
#[test]
fn rename_map_counts_neg_subterms() {
    let mut sys = System::empty();
    sys.subterm_store_mut().neg_subterms =
        SortedPairSet::rebuild_from(vec![(mterm(90), mterm(91))]);
    let rename = compute_rename_map(&sys, &std::collections::BTreeSet::new());
    assert_eq!(rename.get(&mvar(90)), Some(LVar::new("", LSort::Msg, 0)));
    assert_eq!(rename.get(&mvar(91)), Some(LVar::new("", LSort::Msg, 1)));
}

// =========================================================================
// source_bounds
// =========================================================================

/// `boundsVarIdx` (LTerm.hs:672-675) folds the frees of `instance HasFrees
/// System` (System.hs:1832-1877), which reaches the subterm store's NEGATIVE
/// subterms before its positive and solved ones (SubtermStore.hs:546-549).  A
/// variable living in a negative subterm alone therefore sets both ends of
/// the source's bounds, and so both the `matchToGoal` rename shift and the
/// `refineSource` fresh seed.
#[test]
fn bounds_var_idx_of_system_counts_neg_subterms() {
    let mut sys = System::empty();
    sys.subterm_store_mut().neg_subterms =
        SortedPairSet::rebuild_from(vec![(mterm(90), mterm(91))]);
    assert_eq!(tamarin_term::lterm::bounds_var_idx(&sys), Some((90, 91)));
}

/// `source_bounds` splits the two ends of `instance HasFrees Source`
/// (System.hs:1879-1889).  The MIN is over `cdGoal` and every case, because
/// `rename th0` (Sources.hs:268-317, see line 307) rebases the whole source.
/// The MAX is over the cases alone, because `avoid th` (Sources.hs:113-137,
/// see line 128) sees a source whose `cdGoal` has already been overwritten
/// with the live goal.
#[test]
fn source_bounds_takes_the_max_over_cases_only() {
    let goal = Goal::Action(nvar(5), LNFact::new(FactTag::Out, vec![mterm(200)]));
    let mut case_sys = System::empty();
    case_sys.content_mut().last_atom = Some(nvar(20));
    case_sys.subterm_store_mut().neg_subterms =
        SortedPairSet::rebuild_from(vec![(mterm(60), mterm(61))]);
    let src = Source::eager(goal, vec![("case".to_string(), case_sys.clone())], false);

    let cases = vec![("case".to_string(), case_sys)];
    assert_eq!(source_bounds(&src, &cases), (Some(5), Some(61)));
}
