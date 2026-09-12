// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::constraint::constraints::{LessAtom, Reason};
use tamarin_term::lterm::{LSort, LVar};

fn n(name: &str) -> NodeId {
    LVar::new(name, LSort::Node, 0)
}

/// `cyclic` is the `Cyclic` contradiction check over the raw less-relation.
/// It reports a cycle only when the ordering edges close one.  The reflexive
/// case matters here.  `exploitUniqueMsgOrder` inserts `i < i` for a node that
/// both concludes `KD(m)` and carries `KU(m)`.  That self-edge is the only
/// thing that rules out such a case (see
/// `simplify_tests::exploit_unique_msg_order_inserts_the_reflexive_self_edge`).
#[test]
fn cyclic_sees_closed_orderings_only() {
    let ab = LessAtom::new(n("a"), n("b"), Reason::Fresh);
    let bc = LessAtom::new(n("b"), n("c"), Reason::Fresh);
    let ca = LessAtom::new(n("c"), n("a"), Reason::Fresh);
    let aa = LessAtom::new(n("a"), n("a"), Reason::NormalForm);
    for (label, atoms, want) in [
        ("no atoms", vec![], false),
        ("chain a<b<c", vec![ab.clone(), bc.clone()], false),
        ("closed a<b<c<a", vec![ab.clone(), bc, ca], true),
        ("reflexive a<a", vec![aa], true),
        ("single edge", vec![ab], false),
    ] {
        let relation = atoms
            .iter()
            .map(|atom| (atom.smaller, atom.larger))
            .collect();
        assert_eq!(tamarin_utils::dag::cyclic(&relation), want, "{label}");
    }
}

/// `nonInjectiveFactInstances` direct port: feed in a system with
/// an Init→Stop edge for an injective fact `Inj` and a Copy node
/// reachable from Init that also produces/consumes Inj with the
/// same first arg, then check we see exactly one
/// `NonInjectiveFactInstance(i, j, k)` triple.
#[test]
fn non_injective_fact_witness_emitted() {
    use crate::constraint::constraints::{Edge, LessAtom, Reason};
    use crate::constraint::system::System;
    use crate::fact::{Fact, FactTag, Multiplicity};
    use crate::rule::{
        ConcIdx, IntrRuleACInfo, PremIdx, ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleACInst,
        RuleAttributes, RuleInfo,
    };
    use tamarin_term::builtin::msg_var;
    use tamarin_term::maude_proc::MaudeHandle;

    // Build the rule instances.
    let inj_tag = FactTag::Proto(Multiplicity::Linear, "Inj", 1);
    let inj_fact = Fact::new(inj_tag, vec![msg_var("x", 0)]);

    let init: RuleACInst = Rule::new(
        RuleInfo::<ProtoRuleACInstInfo, IntrRuleACInfo>::Proto(ProtoRuleACInstInfo {
            name: ProtoRuleName::Stand("Init"),
            attributes: RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        }),
        vec![],
        vec![inj_fact.clone()],
        vec![],
    );
    let copy: RuleACInst = Rule::new(
        RuleInfo::<ProtoRuleACInstInfo, IntrRuleACInfo>::Proto(ProtoRuleACInstInfo {
            name: ProtoRuleName::Stand("Copy"),
            attributes: RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        }),
        vec![inj_fact.clone()],
        vec![inj_fact.clone()],
        vec![],
    );
    let stop: RuleACInst = Rule::new(
        RuleInfo::<ProtoRuleACInstInfo, IntrRuleACInfo>::Proto(ProtoRuleACInstInfo {
            name: ProtoRuleName::Stand("Stop"),
            attributes: RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        }),
        vec![inj_fact.clone()],
        vec![],
        vec![],
    );

    // Construct a system: i = #1 (Init) → k = #2 (Stop) directly,
    // with j = #3 (Copy) reachable from i and k from j.
    let i = n("1");
    let j = n("3");
    let k = n("2");
    let mut sys = System::empty();
    sys.add_node(i, init);
    sys.add_node(j, copy);
    sys.add_node(k, stop);
    // i → k edge (Inj fact).
    sys.add_edge(Edge {
        src: (i, ConcIdx(0)),
        tgt: (k, PremIdx(0)),
    });
    // i < j, j < k via less atoms.
    sys.add_less(LessAtom::new(i, j, Reason::Adversary));
    sys.add_less(LessAtom::new(j, k, Reason::Adversary));

    // Build the proof context that knows `Inj` is injective.
    let Some(mp) = tamarin_test_support::require_maude_path() else {
        return;
    };
    let h = MaudeHandle::start(&mp, tamarin_term::maude_sig::pair_maude_sig()).unwrap();
    let mut ctx = ProofContext::new(h, Vec::new());
    std::sync::Arc::get_mut(&mut ctx.shared)
        .expect("a fresh context uniquely owns its shared data")
        .injective_fact_insts = [(inj_tag, Vec::new())].into_iter().collect();

    let cs = contradictions(&ctx, &sys);
    let injs: Vec<_> = cs
        .iter()
        .filter(|c| matches!(c, Contradiction::NonInjectiveFactInstance(_, _, _)))
        .collect();
    // The result is exactly the (i, j, k) witness triple, in HS's argument
    // order.  The renderer prints these three ids.  A witness in a different
    // order, or a duplicated witness, therefore changes the printed bytes.  A
    // check for "at least one" witness would let that through.
    assert_eq!(
        injs,
        vec![&Contradiction::NonInjectiveFactInstance(i, j, k)],
        "expected exactly the (Init, Copy, Stop) witness; got {:?}",
        cs
    );
}

/// The pass-shared `NodeRuleMap` is lazy: checks whose early-outs
/// fire must leave the `OnceCell` untouched, while a mismatched-tag
/// edge must both trip `has_incompatible_edge_facts` and populate it.
#[test]
fn shared_node_rule_map_lazy_and_incompatible_edge_detected() {
    use crate::constraint::constraints::{Edge, LessAtom, Reason};
    use crate::constraint::system::System;
    use crate::fact::{Fact, FactTag, Multiplicity};
    use crate::rule::{
        ConcIdx, IntrRuleACInfo, PremIdx, ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleACInst,
        RuleAttributes, RuleInfo,
    };
    use tamarin_term::builtin::msg_var;

    let a_fact = Fact::new(
        FactTag::Proto(Multiplicity::Linear, "A", 1),
        vec![msg_var("x", 0)],
    );
    let b_fact = Fact::new(
        FactTag::Proto(Multiplicity::Linear, "B", 1),
        vec![msg_var("x", 0)],
    );
    let proto = |name: &'static str,
                 prems: Vec<crate::fact::LNFact>,
                 concs: Vec<crate::fact::LNFact>|
     -> RuleACInst {
        Rule::new(
            RuleInfo::<ProtoRuleACInstInfo, IntrRuleACInfo>::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand(name),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            }),
            prems,
            concs,
            vec![],
        )
    };

    // Early-out paths: an Adversary less-atom over non-AC rules and
    // no edges — neither check may force the shared map.
    let i = n("1");
    let k = n("2");
    let mut sys = System::empty();
    sys.add_node(i, proto("Src", vec![], vec![a_fact.clone()]));
    sys.add_node(k, proto("Snk", vec![b_fact.clone()], vec![]));
    sys.add_less(LessAtom::new(i, k, Reason::Adversary));
    let cell = std::cell::OnceCell::new();
    assert!(!has_forbidden_constr_chain(&sys, &cell));
    assert!(!has_incompatible_edge_facts(&sys, &cell));
    assert!(
        cell.get().is_none(),
        "early-outs must not build the shared map"
    );

    // A conclusion-A → premise-B edge is tag-incompatible; detecting
    // it forces the shared map.
    sys.add_edge(Edge {
        src: (i, ConcIdx(0)),
        tgt: (k, PremIdx(0)),
    });
    let cell = std::cell::OnceCell::new();
    assert!(has_incompatible_edge_facts(&sys, &cell));
    assert!(cell.get().is_some());
}

/// The [`NfMemo`] must never change a verdict: every candidate answered
/// from the memo agrees with a fresh `nf_via_haskell_maude_with_sig`
/// call, including for builtin-AC-headed and user-`[AC]`-headed terms
/// (whose st-rule LHSes are matched over Maude).  The second pass
/// rebuilds every term from scratch, so the hits go through `Term`'s
/// content-based `Hash`/`Eq` rather than `Arc` identity.
#[test]
fn nf_memo_agrees_with_unmemoized_verdicts() {
    use tamarin_term::builtin::{fresh_var, hash, msg_var, mult, pair, xor};
    use tamarin_term::function_symbols::{AcFctSym, Constructability, NdcState, NoEqSym, Privacy};
    use tamarin_term::lterm::LNTerm;
    use tamarin_term::maude_proc::MaudeHandle;
    use tamarin_term::rewriting::RRule;
    use tamarin_term::term::f_app_acfct;

    let Some(mp) = tamarin_test_support::require_maude_path() else {
        return;
    };

    // csf26-ac CRxor's shape: `xorr/2 [AC]` with the two cancellation
    // equations, plus the builtin xor / multiset operators so
    // builtin-AC-headed subjects are legal in the emitted MSG module.
    let xorr = AcFctSym::new(
        b"xorr".to_vec(),
        Privacy::Public,
        Constructability::Constructor,
        NdcState::IsNdc,
    );
    let zeroo = NoEqSym::new(
        b"zeroo".to_vec(),
        0,
        Privacy::Public,
        Constructability::Constructor,
    );
    let mut sig = tamarin_term::maude_sig::pair_maude_sig();
    sig.enable_xor = true;
    sig.enable_mset = true;
    sig.st_ac_fun_syms.insert(xorr);
    sig.st_fun_syms.insert(zeroo);
    let (x, y) = (msg_var("x", 0), msg_var("y", 0));
    sig.st_rules.insert(
        tamarin_term::subterm_rule::rrule_to_ctxt_st_rule(&RRule::new(
            f_app_acfct(xorr, vec![x.clone(), x.clone()]),
            tamarin_term::term::f_app_no_eq(zeroo, vec![]),
        ))
        .expect("ground-RHS st rule"),
    );
    sig.st_rules.insert(
        tamarin_term::subterm_rule::rrule_to_ctxt_st_rule(&RRule::new(
            f_app_acfct(
                xorr,
                vec![f_app_acfct(xorr, vec![x.clone(), y.clone()]), x.clone()],
            ),
            y.clone(),
        ))
        .expect("subterm-RHS st rule"),
    );
    let sig = sig.refresh();
    let maude = MaudeHandle::start(&mp, sig.clone()).unwrap();

    // Rebuilt from scratch on each call: pass 2 gets fresh allocations.
    let candidates = || -> Vec<LNTerm> {
        let (k, na) = (fresh_var("k", 0), fresh_var("na", 0));
        let (x, y) = (msg_var("x", 0), msg_var("y", 0));
        vec![
            // user-AC-headed, reducible by `xorr(x, x) = zeroo`
            f_app_acfct(xorr, vec![k.clone(), k.clone()]),
            // user-AC-headed, reducible by the flattened second rule
            f_app_acfct(xorr, vec![k.clone(), k.clone(), y.clone()]),
            // user-AC-headed, irreducible
            f_app_acfct(xorr, vec![k.clone(), na.clone()]),
            // builtin-AC-headed
            xor(k.clone(), na.clone()),
            xor(x.clone(), x.clone()),
            mult(x.clone(), y.clone()),
            // NoEq-headed and bare literals
            pair(hash(x.clone()), na.clone()),
            hash(f_app_acfct(xorr, vec![k.clone(), k.clone()])),
            k,
            x,
        ]
    };

    let mut memo = NfMemo::default();
    let mut verdicts = Vec::new();
    for pass in 0..2 {
        for t in candidates() {
            let expected = tamarin_term::norm::nf_via_haskell_maude_with_sig(&sig, &maude, &t);
            assert_eq!(
                nf_memoized(&sig, &maude, &mut memo, &t),
                expected,
                "pass {pass}: memoized verdict disagrees for {t:?}"
            );
            verdicts.push(expected);
        }
    }
    assert!(
        verdicts.contains(&true) && verdicts.contains(&false),
        "the candidate set must cover both NF and non-NF terms"
    );
    let distinct: BTreeSet<LNTerm> = candidates().into_iter().collect();
    assert_eq!(
        memo.len(),
        distinct.len(),
        "pass 2 must hit existing entries, not add new ones"
    );

    // The walk built on top of the memo agrees with a walk whose memo
    // is empty at every top-level term.
    let irreducible = &sig.irreducible_fun_syms_fast;
    let mut shared = NfMemo::default();
    for t in candidates() {
        let fresh = any_non_nf(&maude, &sig, irreducible, &mut NfMemo::default(), &t);
        assert_eq!(
            any_non_nf(&maude, &sig, irreducible, &mut shared, &t),
            fresh,
            "shared-memo walk disagrees for {t:?}"
        );
    }
}

/// The point of `hasForbiddenConstrChain`: two `c_xor` instances linked
/// by an `Adversary` less-atom, the first's conclusion feeding the
/// second's premises, and BOTH carrying a (nearly-)trivial KU premise —
/// so the component accumulates two trivial instances and the check
/// fires.  Dropping either instance's triviality drops the verdict.
#[test]
fn forbidden_constr_chain_fires_on_two_trivial_xor_instances() {
    use crate::constraint::constraints::{LessAtom, Reason};
    use crate::constraint::system::System;
    use crate::fact::ku_fact;
    use crate::rule::{IntrRuleACInfo, ProtoRuleACInstInfo, Rule, RuleACInst, RuleInfo};
    use tamarin_term::builtin::{hash, msg_var, xor};
    use tamarin_term::function_symbols::{AcSym, FunSym};

    // `c_xor`-shaped construction rule: [KU(a), KU(b)] -> [KU(a⊕b)].
    let c_xor = |prems: Vec<crate::fact::LNFact>, conc: crate::fact::LNFact| -> RuleACInst {
        Rule::new(
            RuleInfo::<ProtoRuleACInstInfo, IntrRuleACInfo>::Intr(IntrRuleACInfo::ConstrRule {
                name: b"_xor".to_vec(),
                fun: FunSym::Ac(AcSym::Xor),
            }),
            prems,
            vec![conc],
            vec![],
        )
    };
    let (i, j) = (n("i"), n("j"));
    let build = |r1: RuleACInst, r2: RuleACInst| -> System {
        let mut sys = System::empty();
        sys.add_node(i, r1);
        sys.add_node(j, r2);
        sys.add_less(LessAtom::new(i, j, Reason::Adversary));
        sys
    };

    // Node i: KU(x), KU(y) -> KU(x⊕y).  `KU(x)` is trivial (msg var).
    // Node j: KU(x⊕y), KU(z) -> KU((x⊕y)⊕z).  `KU(x⊕y)` is nearly
    // trivial for Xor (the symbol applied to msg vars only).
    let (x, y, z) = (msg_var("x", 0), msg_var("y", 0), msg_var("z", 0));
    let xy = xor(x.clone(), y.clone());
    let both_trivial = build(
        c_xor(
            vec![ku_fact(x.clone()), ku_fact(y.clone())],
            ku_fact(xy.clone()),
        ),
        c_xor(
            vec![ku_fact(xy.clone()), ku_fact(z.clone())],
            ku_fact(xor(xy.clone(), z.clone())),
        ),
    );
    assert!(has_forbidden_constr_chain(
        &both_trivial,
        &std::cell::OnceCell::new()
    ));

    // Same linkage, but node i's premises are hashes rather than plain
    // msg vars, so only node j contributes a trivial instance: one is
    // not two, and the check stays silent.
    let (hx, hy) = (hash(x.clone()), hash(y.clone()));
    let hxhy = xor(hx.clone(), hy.clone());
    let one_trivial = build(
        c_xor(vec![ku_fact(hx), ku_fact(hy)], ku_fact(hxhy.clone())),
        c_xor(
            vec![ku_fact(hxhy.clone()), ku_fact(z.clone())],
            ku_fact(xor(hxhy, z)),
        ),
    );
    assert!(!has_forbidden_constr_chain(
        &one_trivial,
        &std::cell::OnceCell::new()
    ));
}

/// `isForbiddenDPMult` (Contradictions.hs) gates ONLY on the
/// structural shape `[KD(pmult(_,p)), KU(b)] -> [KD(pmult(c,p))]` plus
/// `neverContainsFreshPriv p && (niFactors c \\ niFactors b == [])` —
/// there is no `isDPMultRule` rule-name guard. Pin that the Rust port
/// fires on a rule with the pmult shape even when its `info` is NOT a
/// `_pmult` DestrRule (here: a Coerce intruder rule).
#[test]
fn forbidden_d_pmult_fires_without_pmult_rule_name() {
    use crate::fact::{Fact, FactTag};
    use crate::rule::{IntrRuleACInfo, ProtoRuleACInstInfo, Rule, RuleACInst, RuleInfo};
    use tamarin_term::builtin::{msg_var, pmult, pub_var};

    // p (point) is Pub → neverContainsFreshPriv p == true.
    // c == b == msg_var "b" → niFactors c \\ niFactors b == [].
    let p = pub_var("p", 0);
    let b = msg_var("b", 0);
    let s = msg_var("s", 0);
    let kd = |t| Fact::new(FactTag::Kd, vec![t]);
    let ku = |t| Fact::new(FactTag::Ku, vec![t]);

    // info = Coerce, deliberately NOT a `_pmult` DestrRule.
    let ru: RuleACInst = Rule::new(
        RuleInfo::<ProtoRuleACInstInfo, IntrRuleACInfo>::Intr(IntrRuleACInfo::Coerce),
        vec![kd(pmult(s.clone(), p.clone())), ku(b.clone())],
        vec![kd(pmult(b.clone(), p.clone()))],
        vec![],
    );
    assert!(
        !crate::rule::is_d_pmult_rule(&ru),
        "guard precondition: this rule is NOT a _pmult DestrRule"
    );
    assert!(
        super::is_forbidden_d_pmult(&ru),
        "HS isForbiddenDPMult fires on the pmult shape regardless of rule name"
    );
}

#[test]
fn decomposition_symbols_match_recursive_definition() {
    use tamarin_term::function_symbols::{
        exp_sym, pmult_sym, CSym, Constructability, FunSym, NoEqSym, Privacy,
    };
    use tamarin_term::lterm::{LNTerm, Name, NameTag};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::{const_term, var_term, Lit};

    fn public(t: &LNTerm) -> bool {
        match t {
            Term::Lit(Lit::Var(v)) => !matches!(v.sort, LSort::Msg | LSort::Fresh),
            Term::Lit(Lit::Con(n)) => n.tag != NameTag::Fresh,
            Term::App(sym, args) => {
                !matches!(sym, FunSym::NoEq(s) if s.privacy == Privacy::Private)
                    && args.iter().all(public)
            }
        }
    }
    fn reference(t: &LNTerm, prune: bool) -> Option<Vec<RootSym>> {
        if prune && public(t) {
            return Some(vec![]);
        }
        let (mut out, children): (_, &[LNTerm]) = match dh_view(t) {
            Some(DhView::Exp(base)) => (
                vec![RootSym::Sym(FunSym::NoEq(exp_sym()))],
                std::slice::from_ref(base),
            ),
            Some(DhView::PMult(base)) => (
                vec![
                    RootSym::Sym(FunSym::NoEq(exp_sym())),
                    RootSym::Sym(FunSym::NoEq(pmult_sym())),
                    RootSym::Sym(FunSym::C(CSym::EMap)),
                ],
                std::slice::from_ref(base),
            ),
            Some(DhView::EMap) => (vec![RootSym::Sym(FunSym::C(CSym::EMap))], &[]),
            None => (
                vec![root_sym(t)?],
                match t {
                    Term::App(_, args) => args,
                    Term::Lit(_) => &[],
                },
            ),
        };
        for child in children {
            out.extend(reference(child, prune)?);
        }
        Some(out)
    }
    fn next(seed: &mut u64) -> usize {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        (*seed >> 32) as usize
    }
    fn tree(seed: &mut u64, depth: usize, symbols: &[FunSym], leaves: &[LNTerm]) -> LNTerm {
        if depth == 0 || next(seed).is_multiple_of(4) {
            return leaves[next(seed) % leaves.len()].clone();
        }
        let sym = symbols[next(seed) % symbols.len()];
        let count = match sym {
            FunSym::NoEq(s) => s.arity,
            _ => 2,
        };
        Term::App(
            sym,
            (0..count)
                .map(|_| tree(seed, depth - 1, symbols, leaves))
                .collect(),
        )
    }
    let symbols = [
        FunSym::NoEq(NoEqSym::new(
            b"public".to_vec(),
            2,
            Privacy::Public,
            Constructability::Constructor,
        )),
        FunSym::NoEq(NoEqSym::new(
            b"private".to_vec(),
            1,
            Privacy::Private,
            Constructability::Constructor,
        )),
        FunSym::NoEq(NoEqSym::new(
            b"constant".to_vec(),
            0,
            Privacy::Public,
            Constructability::Constructor,
        )),
        FunSym::NoEq(exp_sym()),
        FunSym::NoEq(pmult_sym()),
        FunSym::C(CSym::EMap),
        FunSym::List,
    ];
    let leaves: Vec<LNTerm> = [
        LSort::Msg,
        LSort::Fresh,
        LSort::Pub,
        LSort::Node,
        LSort::Nat,
    ]
    .into_iter()
    .map(|s| var_term(LVar::new("x", s, 0)))
    .chain(
        [
            NameTag::Pub,
            NameTag::Fresh,
            NameTag::Nat,
            NameTag::Node,
            NameTag::Abbrev,
        ]
        .into_iter()
        .map(|tag| const_term(Name::new(tag, "c"))),
    )
    .collect();
    for seed in 0..2000 {
        let t = tree(&mut (seed + 1), 5, &symbols, &leaves);
        assert_eq!(never_contains_fresh_priv(&t), public(&t), "seed {seed}");
        for prune in [false, true] {
            assert!(
                possible_syms(&t, prune) == reference(&t, prune),
                "seed {seed}, prune {prune}"
            );
        }
    }
    // Unknown DH exponents/scalars determine publicness but do not make the
    // symbol result unknown when the emitted base is public.
    for (sym, args) in [
        (
            FunSym::NoEq(exp_sym()),
            vec![leaves[5].clone(), leaves[0].clone()],
        ),
        (
            FunSym::NoEq(pmult_sym()),
            vec![leaves[0].clone(), leaves[5].clone()],
        ),
        (
            FunSym::C(CSym::EMap),
            vec![leaves[0].clone(), leaves[5].clone()],
        ),
    ] {
        let t = Term::App(sym, args.into());
        assert!(!possible_root_syms(&t).unwrap().is_empty());
        assert!(possible_root_syms(&t) == reference(&t, true));
    }
}

#[test]
fn deep_freshness_and_symbol_checks_use_small_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            use tamarin_term::function_symbols::{Constructability, NoEqSym, Privacy};
            use tamarin_term::lterm::pub_term;
            use tamarin_term::term::f_app_no_eq;
            use tamarin_term::vterm::var_term;
            let sym = NoEqSym::new(
                b"h".to_vec(),
                1,
                Privacy::Public,
                Constructability::Constructor,
            );
            for (leaf, public, unknown) in [
                (pub_term("public"), true, false),
                (var_term(LVar::new("fresh", LSort::Fresh, 0)), false, false),
                (var_term(LVar::new("message", LSort::Msg, 0)), false, true),
            ] {
                let mut t = leaf;
                for _ in 0..32768 {
                    t = f_app_no_eq(sym, vec![t]);
                }
                assert_eq!(never_contains_fresh_priv(&t), public);
                let roots = possible_root_syms(&t);
                let ends = possible_end_syms(&t);
                if unknown {
                    assert!(roots.is_none() && ends.is_none());
                } else {
                    assert_eq!(roots.unwrap().len(), if public { 0 } else { 32769 });
                    assert_eq!(ends.unwrap().len(), 32769);
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn symbol_intersection_handles_duplicates_and_empty_sets() {
    let symbols: Vec<_> = [LSort::Msg, LSort::Fresh, LSort::Pub, LSort::Node]
        .into_iter()
        .map(RootSym::Sort)
        .collect();
    for size in [0, 1, 16, 17, 1024] {
        for offset in 0..4 {
            let left: Vec<_> = (0..size).map(|i| symbols[i % 2].clone()).collect();
            let right: Vec<_> = (0..size)
                .map(|i| symbols[(i % 2 + offset) % 4].clone())
                .collect();
            assert_eq!(
                root_symbols_disjoint(&left, &right),
                left.iter().all(|s| !right.contains(s))
            );
        }
    }
}
