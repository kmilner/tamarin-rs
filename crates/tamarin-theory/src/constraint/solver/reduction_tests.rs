// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use tamarin_term::maude_sig::pair_maude_sig;

/// Absolute maude locations probed when `MAUDE_PATH` is unset — the same
/// pair the rest of the workspace's maude-gated suites walk.
const MAUDE_CANDIDATES: [&str; 2] = ["/usr/local/bin/maude", "/usr/bin/maude"];

/// Probed after [`MAUDE_CANDIDATES`] and `$PATH`: this workspace's benchmark
/// toolchain installs maude under linuxbrew, which is not on a default `PATH`.
const MAUDE_BREW: &str = "/home/linuxbrew/.linuxbrew/bin/maude";

/// The first `maude` on `$PATH`, if any.
fn maude_on_path() -> Option<String> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|dir| dir.join("maude"))
        .find(|c| c.is_file())
        .map(|c| c.to_string_lossy().into_owned())
}

/// The maude the tests below run against: `$MAUDE_PATH` when set, else the
/// first of [`MAUDE_CANDIDATES`], `$PATH`, [`MAUDE_BREW`] that exists.
///
/// A `MAUDE_PATH` naming a file that does not exist is a MISCONFIGURATION,
/// not a reason to skip — returning `None` there would turn every
/// maude-backed test in this file green on a CI whose image moved maude.
/// Panic instead, so the run goes red.  Resolving nothing at all is the same
/// failure with a wider blast radius, so it panics too: `TAM_ALLOW_NO_MAUDE=1`
/// is the only way to get the old silent skip, and naming it is a deliberate
/// statement that this run is not asserting anything about maude.
fn maude_path() -> Option<String> {
    if let Ok(p) = std::env::var("MAUDE_PATH") {
        assert!(
            std::path::Path::new(&p).exists(),
            "MAUDE_PATH={p} does not exist; unset it to fall back to \
             {MAUDE_CANDIDATES:?}, or point it at a real maude — skipping \
             every maude-backed test here would report green vacuously"
        );
        return Some(p);
    }
    if let Some(c) = MAUDE_CANDIDATES
        .iter()
        .find(|c| std::path::Path::new(c).exists())
    {
        return Some((*c).to_string());
    }
    if let Some(p) = maude_on_path() {
        return Some(p);
    }
    if std::path::Path::new(MAUDE_BREW).exists() {
        return Some(MAUDE_BREW.to_string());
    }
    if std::env::var("TAM_ALLOW_NO_MAUDE").as_deref() == Ok("1") {
        return None;
    }
    panic!(
        "no maude found: probed $MAUDE_PATH, {MAUDE_CANDIDATES:?}, $PATH and \
         {MAUDE_BREW}.  Every maude-backed test in this file would otherwise \
         report green having run nothing.  Install maude, point MAUDE_PATH at \
         it, or set TAM_ALLOW_NO_MAUDE=1 to accept the silent skip."
    );
}

fn ctx() -> Option<ProofContext> {
    let path = maude_path()?;
    // A maude that resolved but will not start is the same misconfiguration
    // as a dangling MAUDE_PATH: swallowing it with `.ok()?` would silently
    // skip every maude-backed test in this file, so fail loudly instead.
    let h =
        tamarin_term::maude_proc::MaudeHandle::start(&path, pair_maude_sig()).unwrap_or_else(|e| {
            panic!(
                "maude at {path} failed to start: {e:?} — every maude-backed \
                 test here would otherwise skip silently"
            )
        });
    Some(ProofContext::new(h, Vec::new()))
}

#[test]
fn reduction_starts_unchanged() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let r = Reduction::new(&ctx, System::empty());
    assert_eq!(r.changed, ChangeIndicator::Unchanged);
}

/// `ku_vars` must read the two variables `removePermutations` permutes
/// off the AC constructor rules' own `KU(x)`, `KU(y)` premises — and
/// answer `OtherRule` for every other premise shape, including the
/// `KD`-headed destruction rules generated alongside them.
#[test]
fn ku_vars_reads_the_ac_constructor_premise_variables() {
    use crate::rule::{IntrRuleAC, ProtoRuleACInstInfo, Rule, RuleACInst, RuleInfo};
    use tamarin_term::function_symbols::{AcSym, FunSym};

    let inst = |r: &IntrRuleAC| -> RuleACInst {
        Rule::new(
            RuleInfo::<ProtoRuleACInstInfo, _>::Intr(r.info.clone()),
            r.premises.clone(),
            r.conclusions.clone(),
            r.actions.clone(),
        )
    };
    // c_xor / c_mult (`multisetIntruderRules`' union constructor) are
    // the two builtin AC construction rules solveAction can label an
    // AC-headed `KU` goal with.
    for (rules, sym) in [
        (crate::intruder_rules::xor_intruder_rules(), AcSym::Xor),
        (
            crate::intruder_rules::multiset_intruder_rules(),
            AcSym::Union,
        ),
    ] {
        let constr = rules
            .iter()
            .find(|r| crate::rule::is_ac_constr_rule(&inst(r)) == Some(FunSym::Ac(sym)))
            .expect("generator emits one AC construction rule");
        let ru = inst(constr);
        let IsAcConstructor::AcConstructor(v1, v2) = ku_vars(&ru) else {
            panic!("{sym:?} construction rule must yield two KU premise vars");
        };
        // Exactly the rule's own premise variables, in premise order.
        let prem_var = |i: usize| match &*ru.premises[i].terms {
            [tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(v))] => *v,
            other => panic!("premise {i} is not a single-variable fact: {other:?}"),
        };
        assert_eq!(ru.premises[0].tag, crate::fact::FactTag::Ku);
        assert_eq!(ru.premises[1].tag, crate::fact::FactTag::Ku);
        assert_eq!((v1, v2), (prem_var(0), prem_var(1)));
        assert_ne!(v1, v2);

        // The destruction rules from the same generator lead with a
        // `KD` premise, so they carry no permutable variable pair.
        for d in rules
            .iter()
            .filter(|r| matches!(r.info, crate::rule::IntrRuleACInfo::DestrRule { .. }))
        {
            assert_eq!(
                ku_vars(&inst(d)),
                IsAcConstructor::OtherRule,
                "destruction rule must not claim an AC-constructor var pair"
            );
        }
    }
}

#[test]
fn insert_goal_marks_changed() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    let v = tamarin_term::lterm::LVar::new("k", tamarin_term::lterm::LSort::Msg, 0);
    let f = crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]);
    r.insert_goal(Goal::Action(v, f));
    assert_eq!(r.changed, ChangeIndicator::Changed);
    assert_eq!(r.sys.goals.len(), 1);
}

#[test]
fn solve_term_eqs_trivial_equation_no_change() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    // x =? x is trivially true.
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let t: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    let r_out = r
        .solve_term_eqs(
            SplitStrategy::SplitNow,
            &[tamarin_term::rewriting::Equal {
                lhs: t.clone(),
                rhs: t,
            }],
        )
        .expect("solve");
    assert!(matches!(
        r_out,
        SolveOutcome::Linear(ChangeIndicator::Unchanged)
    ));
}

#[test]
fn solve_term_eqs_unifies_two_vars() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    // x =? y produces a single mgu.
    use tamarin_term::vterm::Lit;
    let x = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    let y = tamarin_term::lterm::LVar::new("y", tamarin_term::lterm::LSort::Msg, 0);
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(x));
    let ty: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(y));
    let r_out = r
        .solve_term_eqs(
            SplitStrategy::SplitNow,
            &[tamarin_term::rewriting::Equal { lhs: tx, rhs: ty }],
        )
        .expect("solve");
    assert!(matches!(
        r_out,
        SolveOutcome::Linear(ChangeIndicator::Changed)
    ));
    assert_eq!(r.changed, ChangeIndicator::Changed);
}

// =====================================================================
// subst_system — Haskell-equivalent invariants
// =====================================================================
//
// Haskell's `Theory.Constraint.Solver.Reduction.substSystem`:
//   substSystem = do
//     c1 <- substNodes
//     substEdges
//     substLastAtom
//     substLessAtoms
//     ...
//     c2 <- substGoals
//     return (c1 <> c2)
// pulls the eq-store substitution through every node id, edge,
// less atom, last atom, and goal. The Rust port should preserve
// these invariants on completion.

#[test]
fn subst_system_rewrites_edge_node_ids_through_eqstore() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    // Force `i_2 = j_3` into the eq-store, then add an edge whose
    // src is `i_2` and confirm that subst_system rewrites it.
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::vterm::Lit;
    let i = LVar::new("i", LSort::Node, 2);
    let j = LVar::new("j", LSort::Node, 3);
    let ti = tamarin_term::term::Term::Lit(Lit::Var(i));
    let tj = tamarin_term::term::Term::Lit(Lit::Var(j));
    // Add an edge i -> some target. (Source-only is enough — we
    // just want to verify the substitution propagates.)
    let tgt = LVar::new("t", LSort::Node, 99);
    r.sys.invalidate_max_var_idx_cache();
    r.sys
        .content_mut()
        .edges
        .push(crate::constraint::constraints::Edge {
            src: (i, crate::rule::ConcIdx(0)),
            tgt: (tgt, crate::rule::PremIdx(0)),
        });
    // Inject the equality into the eq-store directly.
    r.solve_term_eqs(
        SplitStrategy::SplitNow,
        &[tamarin_term::rewriting::Equal { lhs: ti, rhs: tj }],
    )
    .expect("solve");
    r.subst_system();
    // After subst_system, the edge's source node id must be
    // mapped to whatever the canonical representative of i and j
    // is (the eq-store unifier picks one).
    let canonical = {
        let id_term = tamarin_term::term::Term::Lit(Lit::Var(i));
        let mapped = tamarin_term::subst::apply_vterm(&r.sys.eq_store.subst, id_term);
        if let tamarin_term::term::Term::Lit(Lit::Var(v)) = mapped {
            v
        } else {
            i
        }
    };
    assert_eq!(
        r.sys.edges[0].src.0, canonical,
        "edge src should be the canonical node id after subst_system"
    );
}

#[test]
fn subst_system_rewrites_less_atom_node_ids() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::vterm::Lit;
    let i = LVar::new("i", LSort::Node, 2);
    let j = LVar::new("j", LSort::Node, 3);
    let target = LVar::new("t", LSort::Node, 9);
    r.sys.invalidate_max_var_idx_cache();
    r.sys
        .content_mut()
        .less_atoms
        .push(crate::constraint::constraints::LessAtom::new(
            i,
            target,
            crate::constraint::constraints::Reason::Formula,
        ));
    let ti = tamarin_term::term::Term::Lit(Lit::Var(i));
    let tj = tamarin_term::term::Term::Lit(Lit::Var(j));
    r.solve_term_eqs(
        SplitStrategy::SplitNow,
        &[tamarin_term::rewriting::Equal { lhs: ti, rhs: tj }],
    )
    .expect("solve");
    r.subst_system();
    // The less atom's `smaller` should still resolve to the same
    // canonical id reachable from i via the eq-store.
    let canonical = {
        let id_term = tamarin_term::term::Term::Lit(Lit::Var(i));
        let mapped = tamarin_term::subst::apply_vterm(&r.sys.eq_store.subst, id_term);
        if let tamarin_term::term::Term::Lit(Lit::Var(v)) = mapped {
            v
        } else {
            i
        }
    };
    assert_eq!(r.sys.less_atoms[0].smaller, canonical);
}

#[test]
fn subst_system_idempotent_on_empty_substitution() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    // No equations injected — the eq-store substitution is empty.
    let before_changed = r.changed;
    r.subst_system();
    // No-op: nothing to rewrite.
    assert_eq!(r.changed, before_changed);
    assert!(r.sys.nodes.is_empty());
    assert!(r.sys.edges.is_empty());
    assert!(r.sys.less_atoms.is_empty());
}

#[test]
fn subst_system_marks_contradiction_on_shape_mismatch() {
    // Two nodes with the same canonical id but DIFFERENT rule
    // shapes (e.g. one with 0 conclusions, one with 1) cannot be
    // merged consistently — Haskell's `setNodes` reaches the same
    // conclusion via `solveRuleEqs` failing. Our port pushes
    // `gfalse` so the next contradictions check trips.
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::vterm::Lit;
    let i = LVar::new("i", LSort::Node, 2);
    let j = LVar::new("j", LSort::Node, 3);
    let info = || {
        crate::rule::RuleInfo::Proto(crate::rule::ProtoRuleACInstInfo {
            name: crate::rule::ProtoRuleName::Stand("R"),
            attributes: crate::rule::RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        })
    };
    // First node has 0 conclusions; second has 1 — incompatible.
    r.sys
        .add_node(i, crate::rule::Rule::new(info(), vec![], vec![], vec![]));
    let dummy_fact = crate::fact::Fact::new(crate::fact::FactTag::Out, vec![]);
    r.sys.add_node(
        j,
        crate::rule::Rule::new(info(), vec![], vec![dummy_fact], vec![]),
    );
    // Force i = j into the eq-store.
    let ti = tamarin_term::term::Term::Lit(Lit::Var(i));
    let tj = tamarin_term::term::Term::Lit(Lit::Var(j));
    r.solve_term_eqs(
        SplitStrategy::SplitNow,
        &[tamarin_term::rewriting::Equal { lhs: ti, rhs: tj }],
    )
    .expect("solve");
    r.subst_system();
    let bot = crate::guarded::gfalse();
    assert!(
        crate::guarded::stores_contains(&r.sys.formulas, &bot),
        "shape mismatch must push gfalse onto the formula list"
    );
}

#[test]
fn subst_system_merges_collided_nodes_and_equates_their_rules() {
    // When two nodes collapse to the same canonical id, Haskell's
    // `setNodes` runs `solveRuleEqs` on their facts. Our port queues
    // those into solve_fact_eqs at the tail of subst_system. Verify
    // that the merge happens and only one node remains under the
    // canonical id.
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::vterm::Lit;
    let i = LVar::new("i", LSort::Node, 2);
    let j = LVar::new("j", LSort::Node, 3);
    // Two empty rule instances, one keyed by i and one by j.
    let ru = || crate::rule::Rule {
        info: crate::rule::RuleInfo::Proto(crate::rule::ProtoRuleACInstInfo {
            name: crate::rule::ProtoRuleName::Stand("R"),
            attributes: crate::rule::RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        }),
        premises: vec![],
        conclusions: vec![],
        actions: vec![],
        new_vars: vec![],
    };
    r.sys.add_node(i, ru());
    r.sys.add_node(j, ru());
    let ti = tamarin_term::term::Term::Lit(Lit::Var(i));
    let tj = tamarin_term::term::Term::Lit(Lit::Var(j));
    r.solve_term_eqs(
        SplitStrategy::SplitNow,
        &[tamarin_term::rewriting::Equal { lhs: ti, rhs: tj }],
    )
    .expect("solve");
    r.subst_system();
    assert_eq!(
        r.sys.nodes.len(),
        1,
        "two nodes with the same canonical id should merge"
    );
}

#[test]
fn solve_fact_eqs_tag_mismatch_is_contradictory() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    let f1 = crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]);
    let f2 = crate::fact::LNFact::new(crate::fact::FactTag::In, vec![]);
    let r_out = r
        .solve_fact_eqs(
            SplitStrategy::SplitNow,
            &[tamarin_term::rewriting::Equal { lhs: f1, rhs: f2 }],
        )
        .expect("solve");
    assert!(matches!(r_out, SolveOutcome::Contradictory));
}

#[test]
fn solve_disj_goal_empty_is_contradictory() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    let d = Disj(Vec::<Guarded>::new());
    let out = r.solve_disj_goal(&d);
    assert!(matches!(out, GoalCases::Contradictory));
}

#[test]
fn solve_disj_goal_singleton_is_linear() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    // Use gtrue() = Conj([]): it gets decomposed into solved_formulas
    // by insert_formula (not raw-pushed to formulas).
    let f = crate::guarded::gtrue();
    let d = Disj(vec![f.clone()]);
    r.insert_goal(Goal::Disj(d.clone()));
    let out = r.solve_disj_goal(&d);
    // Haskell `solveDisjunction` has no singleton special-case: a lone
    // alternative is named `case_1` (and `ppCases` only elides the
    // heading for the empty name), so the Rust continuation is a
    // single named linear case `case_1`, not an unnamed `Linear`.
    assert!(matches!(&out, GoalCases::LinearNamed(n) if n == "case_1"));
    // gtrue (Conj []) decomposes to solved_formulas — see
    // insert_formula_inner for the Conj arm.
    assert!(crate::guarded::stores_contains(&r.sys.solved_formulas, &f));
    assert!(r
        .sys
        .goals
        .iter()
        .any(|(g, s)| matches!(g, Goal::Disj(_)) && s.solved));
}

#[test]
fn solve_disj_goal_two_branches_forks() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    let f1 = crate::guarded::gtrue(); // Conj([]) → solved_formulas
    let f2 = crate::guarded::gfalse(); // Disj([]) → formulas (gfalse sentinel)
    let d = Disj(vec![f1.clone(), f2.clone()]);
    r.insert_goal(Goal::Disj(d.clone()));
    let out = r.solve_disj_goal(&d);
    match out {
        GoalCases::Cases(systems) => {
            assert_eq!(systems.len(), 2);
            assert!(crate::guarded::stores_contains(
                &systems[0].1.solved_formulas,
                &f1
            ));
            assert!(crate::guarded::stores_contains(&systems[1].1.formulas, &f2));
            for (_, s) in &systems {
                assert!(s
                    .goals
                    .iter()
                    .any(|(g, st)| matches!(g, Goal::Disj(_)) && st.solved));
            }
        }
        other => panic!("expected Cases, got {:?}", other),
    }
}

#[test]
fn solve_subterm_goal_marks_solved_and_moves() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut sys = System::empty();
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    let w = tamarin_term::lterm::LVar::new("y", tamarin_term::lterm::LSort::Msg, 0);
    let tx: tamarin_term::lterm::LNTerm =
        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(v));
    let ty: tamarin_term::lterm::LNTerm =
        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(w));
    sys.invalidate_max_var_idx_cache();
    sys.subterm_store_mut().add(tx.clone(), ty.clone());
    sys.add_goal(Goal::Subterm((tx.clone(), ty.clone())));
    let mut r = Reduction::new(&ctx, sys);
    let out = r.solve_subterm_goal(&(tx.clone(), ty.clone()));
    // `x:msg ⊏ y:msg`: big is a bare variable, so `splitSubterm`
    // (singleStep) cannot decompose ⇒ a single `SubtermD (x,y)` leaf.
    // HS `solveSubterm` therefore emits ONE case `SubtermSplit1`,
    // moves (x,y) into solvedSubterms, and re-adds (x,y) into
    // posSubterms via the SubtermD arm's `addSubterm` (the next
    // simplify drops it again via `posSubterms \ solvedSubterms`).
    assert!(matches!(&out, GoalCases::LinearNamed(n) if n == "SubtermSplit1"));
    assert_eq!(r.sys.subterm_store.subterms.len(), 1);
    assert_eq!(r.sys.subterm_store.solved_subterms.len(), 1);
    assert!(r
        .sys
        .goals
        .iter()
        .any(|(g, s)| matches!(g, Goal::Subterm(_)) && s.solved));
}

#[test]
fn solve_subterm_self_is_contradictory() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut sys = System::empty();
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    let tx: tamarin_term::lterm::LNTerm =
        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(v));
    sys.invalidate_max_var_idx_cache();
    sys.subterm_store_mut().add(tx.clone(), tx.clone());
    let mut r = Reduction::new(&ctx, sys);
    let out = r.solve_subterm_goal(&(tx.clone(), tx));
    assert!(matches!(out, GoalCases::Contradictory));
    assert!(r.sys.subterm_store.contradictory);
}

/// When the goal's existing node already has the matching action,
/// `solve_action_goal` emits `GoalCases::LinearNamed(rule_case_name)`
/// rather than bare `Linear` — mirrors HS `solveAction`'s `Just ru ->
/// ... return ru` arm (Goals.hs) whose surrounding `showRuleCaseName
/// <$>` (Goals.hs:217-252, see line 223) unconditionally emits the rule's case name.
#[test]
fn solve_action_goal_existing_node_with_action_is_linear_named() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    // Build a system with a node already labelled by a rule that
    // produces the action `Out(x)`.
    let mut sys = System::empty();
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    let fa = crate::fact::out_fact(tx);
    let ru: crate::rule::RuleACInst = crate::rule::Rule::new(
        crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::ISend),
        vec![],
        vec![],
        vec![fa.clone()],
    );
    sys.add_node(i, ru);
    sys.add_goal(Goal::Action(i, fa.clone()));
    let mut r = Reduction::new(&ctx, sys);
    let out = r.solve_action_goal(&i, &fa);
    // The case name must be present (showRuleCaseName ru) for the proof
    // tree to render `case <name>` correctly.  Accept any non-empty name.
    match &out {
        GoalCases::LinearNamed(name) => {
            assert!(!name.is_empty(), "rule case name must be non-empty")
        }
        other => panic!("expected GoalCases::LinearNamed, got {:?}", other),
    }
    assert!(r
        .sys
        .goals
        .iter()
        .any(|(g, s)| matches!(g, Goal::Action(_, _)) && s.solved));
}

#[test]
fn solve_action_goal_no_node_no_rules_is_contradictory() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    let fa = crate::fact::out_fact(tx);
    let out = r.solve_action_goal(&i, &fa);
    // No rules in the context → no candidates.
    assert!(matches!(out, GoalCases::Contradictory));
}

#[test]
fn solve_action_goal_no_node_with_matching_rule_unifies() {
    let ctx_no = match ctx() {
        Some(c) => c,
        None => return,
    };
    // Build a context with one rule that has an Out(y) action.
    let v = tamarin_term::lterm::LVar::new("y", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let ty: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    let fact_y = crate::fact::out_fact(ty);
    let rule: crate::rule::ProtoRuleE = crate::rule::Rule::new(
        crate::rule::ProtoRuleEInfo::standard("Send"),
        vec![],
        vec![],
        vec![fact_y],
    );
    let open = crate::theory::OpenProtoRule::new(rule);
    let mut ctx2 = ctx_no.clone();
    ctx2.rules = vec![open];
    let mut r = Reduction::new(&ctx2, System::empty());
    // Goal: Out(x) at fresh node i.
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let v2 = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v2));
    let fa = crate::fact::out_fact(tx);
    let out = r.solve_action_goal(&i, &fa);
    // One matching rule with one matching action ⇒ LinearNamed
    // (the rule name); node added in-place to r.sys.
    assert!(
        matches!(&out, GoalCases::LinearNamed(n) if n == "Send"),
        "expected LinearNamed(\"Send\"), got {:?}",
        out
    );
    assert_eq!(r.sys.nodes.len(), 1);
    assert_eq!(r.sys.nodes[0].0, i);
}

#[test]
fn solve_premise_goal_no_user_rules_uses_intruder() {
    // With the intruder rules wired into ProofContext, an `In(x)`
    // premise can be discharged via `ISend` even when no user
    // rules exist. Tests that the intruder-rule fallback works.
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    let fa = crate::fact::in_fact(tx);
    let p = (i, crate::rule::PremIdx(0));
    let out = r.solve_premise_goal(&p, &fa);
    // ISend supplier can satisfy the In(x) premise → LinearNamed.
    assert!(
        matches!(out, GoalCases::LinearNamed(_)),
        "expected LinearNamed, got {:?}",
        out
    );
}

#[test]
fn solve_premise_goal_no_user_rules_unmatchable_fact_is_contradictory() {
    // Use a fact tag that no intruder rule produces (e.g. a
    // user-defined linear `Foo(x)` fact in an empty context).
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    let fa = crate::fact::Fact::new(
        crate::fact::FactTag::Proto(crate::fact::Multiplicity::Linear, "Foo", 1),
        vec![tx],
    );
    let p = (i, crate::rule::PremIdx(0));
    let out = r.solve_premise_goal(&p, &fa);
    assert!(matches!(out, GoalCases::Contradictory));
}

#[test]
fn solve_premise_goal_with_matching_rule_inserts_edge() {
    let base = match ctx() {
        Some(c) => c,
        None => return,
    };
    // Rule that produces an Out(y) conclusion.
    let v = tamarin_term::lterm::LVar::new("y", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let ty: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    let conc_y = crate::fact::out_fact(ty);
    let rule: crate::rule::ProtoRuleE = crate::rule::Rule::new(
        crate::rule::ProtoRuleEInfo::standard("Producer"),
        vec![],
        vec![conc_y],
        vec![],
    );
    let open = crate::theory::OpenProtoRule::new(rule);
    let mut ctx2 = base.clone();
    ctx2.rules = vec![open];
    let mut r = Reduction::new(&ctx2, System::empty());
    // Premise: Out(x) at node i, premise idx 0.
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 5);
    let v2 = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v2));
    let fa = crate::fact::out_fact(tx);
    let p = (i, crate::rule::PremIdx(0));
    let out = r.solve_premise_goal(&p, &fa);
    // Single matching rule → LinearNamed("Producer"); node + edge
    // applied in-place to r.sys.
    assert!(
        matches!(&out, GoalCases::LinearNamed(n) if n == "Producer"),
        "expected LinearNamed(\"Producer\"), got {:?}",
        out
    );
    assert_eq!(r.sys.nodes.len(), 1);
    assert_eq!(r.sys.edges.len(), 1);
    assert_eq!(r.sys.edges[0].tgt, p);
}

#[test]
fn solve_premise_goal_kd_fact_inserts_irecv_chain() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    let fa = crate::fact::kd_fact(tx);
    let p = (i, crate::rule::PremIdx(0));
    let _out = r.solve_premise_goal(&p, &fa);
    // KD branch inserts IRecv + Chain goal; the Out(mLearn) premise
    // is recursively solved inline (Haskell's solvePremise behaviour)
    // so it does NOT remain as a queued Premise goal.  The recursive
    // solve picks some producer (or Contradictory if there's none in
    // an empty test ctx); the structural invariants we check here are
    // just the IRecv node and chain goal.
    assert!(r.sys.nodes.iter().any(|(_, ru)| matches!(
        ru.info,
        crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::IRecv)
    )));
    assert!(r
        .sys
        .goals
        .iter()
        .any(|(g, _)| matches!(g, Goal::Chain(_, _))));
}

#[test]
fn solve_chain_goal_missing_node_is_contradictory() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let j = tamarin_term::lterm::LVar::new("j", tamarin_term::lterm::LSort::Node, 0);
    let c = (i, crate::rule::ConcIdx(0));
    let p = (j, crate::rule::PremIdx(0));
    let out = r.solve_chain_goal(&c, &p);
    assert!(matches!(out, GoalCases::Contradictory));
}

#[test]
fn solve_chain_goal_compatible_facts_inserts_edge() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    // Build two nodes whose conc/prem facts are compatible.
    let mut sys = System::empty();
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let j = tamarin_term::lterm::LVar::new("j", tamarin_term::lterm::LSort::Node, 0);
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    // Node i conclusion: KD(x).
    let conc_kd = crate::fact::kd_fact(tx.clone());
    let ru_i: crate::rule::RuleACInst = crate::rule::Rule::new(
        crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::IRecv),
        vec![],
        vec![conc_kd],
        vec![],
    );
    sys.add_node(i, ru_i);
    // Node j premise: KD(x).
    let prem_kd = crate::fact::kd_fact(tx);
    let ru_j: crate::rule::RuleACInst = crate::rule::Rule::new(
        crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::ISend),
        vec![prem_kd],
        vec![],
        vec![],
    );
    sys.add_node(j, ru_j);
    let c = (i, crate::rule::ConcIdx(0));
    let p = (j, crate::rule::PremIdx(0));
    sys.add_goal(Goal::Chain(c, p));
    let mut r = Reduction::new(&ctx, sys);
    let out = r.solve_chain_goal(&c, &p);
    // Compatible facts → LinearNamed (rule-named) with edge added
    // and chain goal marked solved in-place.
    assert!(
        matches!(out, GoalCases::LinearNamed(_)),
        "expected LinearNamed, got {:?}",
        out
    );
    assert_eq!(r.sys.edges.len(), 1);
    assert!(r
        .sys
        .goals
        .iter()
        .any(|(g, s)| matches!(g, Goal::Chain(_, _)) && s.solved));
}

#[test]
fn insert_atom_action_creates_action_goal() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    use tamarin_parser::ast::{Atom, Fact, SortHint, Term, VarSpec};
    let mkvar = |n: &str, sort: SortHint| {
        Term::Var(VarSpec {
            name: n.to_string(),
            idx: 0,
            sort,
            typ: None,
        })
    };
    let action = Atom::Action(
        Fact {
            persistent: false,
            annotations: Vec::new(),
            name: "Setup".into(),
            args: vec![mkvar("k", SortHint::Msg)],
        },
        mkvar("i", SortHint::Node),
    );
    let ok = r.insert_atom(&action);
    assert!(ok);
    assert_eq!(r.sys.goals.len(), 1);
    assert!(matches!(&r.sys.goals[0].0, Goal::Action(_, fact)
            if fact.tag == crate::fact::FactTag::Proto(
                crate::fact::Multiplicity::Linear, "Setup", 1)));
}

#[test]
fn insert_atom_less_creates_less_atom() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    use tamarin_parser::ast::{Atom, SortHint, Term, VarSpec};
    let mkvar = |n: &str| {
        Term::Var(VarSpec {
            name: n.to_string(),
            idx: 0,
            sort: SortHint::Node,
            typ: None,
        })
    };
    let less = Atom::Less(mkvar("i"), mkvar("j"));
    let ok = r.insert_atom(&less);
    assert!(ok);
    assert_eq!(r.sys.less_atoms.len(), 1);
}

#[test]
fn insert_atom_last_sets_last_atom() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    use tamarin_parser::ast::{Atom, SortHint, Term, VarSpec};
    let v = Term::Var(VarSpec {
        name: "i".into(),
        idx: 0,
        sort: SortHint::Node,
        typ: None,
    });
    let last = Atom::Last(v);
    assert!(r.insert_atom(&last));
    assert!(r.sys.last_atom.is_some());
}

#[test]
fn solve_action_with_fresh_premise_adds_fresh_supplier() {
    let base = match ctx() {
        Some(c) => c,
        None => return,
    };
    // Setup-like rule: [ Fr(~k) ] --[ Setup(~k) ]-> [ Out(~k) ]
    let v = tamarin_term::lterm::LVar::new("k", tamarin_term::lterm::LSort::Fresh, 0);
    use tamarin_term::vterm::Lit;
    let tk: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    let prem = crate::fact::fresh_fact(tk.clone());
    let act = crate::fact::Fact::new(
        crate::fact::FactTag::Proto(crate::fact::Multiplicity::Linear, "Setup", 1),
        vec![tk.clone()],
    );
    let conc = crate::fact::out_fact(tk);
    let rule: crate::rule::ProtoRuleE = crate::rule::Rule::new(
        crate::rule::ProtoRuleEInfo::standard("Setup"),
        vec![prem],
        vec![conc],
        vec![act],
    );
    let open = crate::theory::OpenProtoRule::new(rule);
    let mut ctx2 = base.clone();
    ctx2.rules = vec![open];
    let mut r = Reduction::new(&ctx2, System::empty());

    // Goal: Setup(x) at fresh node i.
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let v2 = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 1);
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v2));
    let fa = crate::fact::Fact::new(
        crate::fact::FactTag::Proto(crate::fact::Multiplicity::Linear, "Setup", 1),
        vec![tx],
    );
    let out = r.solve_action_goal(&i, &fa);
    // LinearNamed("Setup") with in-place mutation: 2 nodes (Setup
    // instance + Fresh supplier) and 1 edge in r.sys.
    assert!(
        matches!(&out, GoalCases::LinearNamed(n) if n == "Setup"),
        "expected LinearNamed(\"Setup\"), got {:?}",
        out
    );
    assert_eq!(
        r.sys.nodes.len(),
        2,
        "expected 2 nodes (Setup + Fresh supplier), got {}",
        r.sys.nodes.len()
    );
    assert_eq!(r.sys.edges.len(), 1, "expected 1 edge");
}

#[test]
fn while_changing_terminates() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    let mut count = 0;
    r.while_changing(|red| {
        count += 1;
        if count < 3 {
            let v =
                tamarin_term::lterm::LVar::new("k", tamarin_term::lterm::LSort::Msg, count as u64);
            let f = crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]);
            red.insert_goal(Goal::Action(v, f));
            ChangeIndicator::Changed
        } else {
            ChangeIndicator::Unchanged
        }
    });
    assert!(count >= 3);
}

// =========================================================================
// Haskell-faithfulness invariants for case-naming.
//
// Mirrors Haskell's `casName` (Reduction.hs) which uses 1-INDEXED
// `case_<n>` for generic case labels.  Off-by-one here makes
// `distinguish` (ProofMethod.hs:282-339, see line 334) disambiguate against the
// wrong sibling suffix and the proof skeleton drifts.
// =========================================================================

/// `default_case_name(i)` produces `case_<i+1>` — 1-INDEXED.
///
/// Mirrors Haskell's `casName` convention; an off-by-one here regresses
/// the `case split` cluster.  Disjunction-driven case
/// labels (`case_1`, `case_2`, ...) must match the Haskell printer
/// exactly or proof-skeleton diffs report spurious mismatches.
#[test]
fn default_case_name_is_one_indexed() {
    assert_eq!(default_case_name(0), "case_1");
    assert_eq!(default_case_name(1), "case_2");
    assert_eq!(default_case_name(9), "case_10");
    assert_eq!(
        default_case_name(99),
        "case_100",
        "three-digit suffix renders without padding"
    );
}

/// `default_case_name(i) != default_case_name(j)` for i != j —
/// pairwise distinct.  This guards against accidentally returning
/// "case_1" for every i (e.g. a hardcoded constant slipped in).
#[test]
fn default_case_name_is_injective() {
    let n = 25usize;
    let names: Vec<String> = (0..n).map(default_case_name).collect();
    let unique: std::collections::BTreeSet<&String> = names.iter().collect();
    assert_eq!(
        unique.len(),
        n,
        "default_case_name must produce {} distinct names; got {}",
        n,
        unique.len()
    );
}

/// Build a `∀[].[Less #i #j].⊥` GGuarded value — the negated-
/// `Less`-of-node-ids idiom HS calls `markAsSolved`+decompose on
/// (Reduction.hs:461-486).
fn neg_less_node_universal(i_name: &str, j_name: &str) -> Guarded {
    use crate::guarded::{atom_to_gatom_free, GAtom, Quant};
    use tamarin_parser::ast::{Atom, SortHint, Term, VarSpec};
    let mkvar = |n: &str| {
        Term::Var(VarSpec {
            name: n.to_string(),
            idx: 0,
            sort: SortHint::Node,
            typ: None,
        })
    };
    let guard: GAtom = atom_to_gatom_free(&Atom::Less(mkvar(i_name), mkvar(j_name)));
    Guarded::GGuarded {
        qua: Quant::All,
        vars: Vec::new().into(),
        guards: vec![guard].into(),
        body: std::sync::Arc::new(crate::guarded::gfalse()),
    }
}

/// HS-faithful `markAsSolved = when mark $ modM sSolvedFormulas
/// $ S.insert fm` (Reduction.hs:427-494, see line 494).  Children of a Conj/Ex body
/// recurse via `insert' False`, so a negated-atom universal that
/// arrives transitively MUST NOT push into `solved_formulas`.
///
/// The four `solved_formulas.push` sites (Less-node-id, Eq-node-id,
/// Last, Subterm CR-rules) are gated on `mark`.
/// This test exercises the Less-node-id arm:
///   - `insert_formula_inner(_, mark=false)` must leave
///     `solved_formulas` untouched.
///   - `insert_formula_inner(_, mark=true)` (the top-level
///     `insert_formula` entrypoint) must push the formula.
///     Both calls produce the same decomposition (`#i = #j ∨ #j < #i`).
#[test]
fn insert_formula_negated_less_mark_false_does_not_push_solved() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    let g = neg_less_node_universal("i", "j");
    assert!(
        r.sys.solved_formulas.is_empty(),
        "precondition: solved_formulas starts empty"
    );
    // mark=false (the Conj/Ex-body-recursion case).
    r.insert_formula_inner(g.clone(), false);
    assert!(
        !crate::guarded::stores_contains(&r.sys.solved_formulas, &g),
        "mark=false MUST NOT push the negated-Less universal into \
             solved_formulas — HS `markAsSolved` is `when mark $ ...` \
             (Reduction.hs:491).  Pushing unconditionally inflates \
             sSolvedFormulas (Yubikey slightly_weaker_invariant: 3 vs 4)."
    );
}

#[test]
fn insert_formula_negated_less_mark_true_pushes_solved() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut r = Reduction::new(&ctx, System::empty());
    let g = neg_less_node_universal("i", "j");
    // mark=true (the top-level entrypoint).
    r.insert_formula_inner(g.clone(), true);
    assert!(
        crate::guarded::stores_contains(&r.sys.solved_formulas, &g),
        "mark=true (top-level `insert_formula`) MUST push the \
             negated-Less universal into solved_formulas — \
             HS `markAsSolved` fires (Reduction.hs:491)."
    );
}
