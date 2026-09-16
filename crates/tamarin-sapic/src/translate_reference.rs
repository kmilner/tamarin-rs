// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Bounded original traversal and NDC rewrite oracle. Primitive translations are shared.
use super::*;
fn generate_rules_reference<'a>(
    ctx: &TransCtx,
    an_proc: &'a Process<ProcessAnnotation<LVar>, SapicLVar>,
    p: &ProcessPosition,
    tildex: &BTreeSet<LVar>,
) -> Result<Vec<AnnotatedRule<'a, ProcessAnnotation<LVar>>>, String> {
    let proc = tamarin_theory::sapic::process_at(an_proc, p)
        .ok_or_else(|| format!("gen: invalid position {p:?}"))?;
    match proc {
        Process::Null(_) => {
            // `trans_null` is the identity wrapper for progress/reliable.
            let bodies = base_trans_null(p, tildex);
            Ok(map_to_annotated_rule(proc, p, bodies))
        }
        Process::Action(ac, ann, _) => {
            let (bodies, tildex2) = trans_action(ctx, ac, ann, p, tildex)?;
            let mut here = map_to_annotated_rule(proc, p, bodies);
            let mut child_pos = p.clone();
            child_pos.push(1);
            let rest = generate_rules_reference(ctx, an_proc, &child_pos, &tildex2)?;
            here.extend(rest);
            Ok(here)
        }
        // NDC special case (sapic/src/Sapic.hs:123-127): the NDC node itself emits NO
        // rule; its two children SHARE the parent's state position.  We
        // translate each child at `p++[1]` / `p++[2]` (so rule names carry the
        // correct position suffix), then rewrite the State premise of EVERY
        // generated rule from the child position back to the parent `p`
        // (`substStatePos`).
        Process::Comb(ProcessCombinator::Ndc, _, _, _) => {
            let mut pl = p.clone();
            pl.push(1);
            let mut pr = p.clone();
            pr.push(2);
            let l = generate_rules_reference(ctx, an_proc, &pl, tildex)?;
            let r = generate_rules_reference(ctx, an_proc, &pr, tildex)?;
            let mut out = subst_state_pos_rules(l, &pl, p);
            out.extend(subst_state_pos_rules(r, &pr, p));
            Ok(out)
        }
        // General combinator (sapic/src/Sapic.hs:128-134): emit this node's own rules,
        // then recurse into the left child with `tildex'1` and (if present) the
        // right child with `tildex'2`.
        Process::Comb(c, ann, _, _) => {
            let (bodies, tildex_l, tildex_r) = trans_comb(ctx, c, ann, p, tildex)?;
            let mut here = map_to_annotated_rule(proc, p, bodies);
            let mut pl = p.clone();
            pl.push(1);
            let msrs_l = generate_rules_reference(ctx, an_proc, &pl, &tildex_l)?;
            here.extend(msrs_l);
            if let Some(tx_r) = tildex_r {
                let mut pr = p.clone();
                pr.push(2);
                let msrs_r = generate_rules_reference(ctx, an_proc, &pr, &tx_r)?;
                here.extend(msrs_r);
            }
            Ok(here)
        }
    }
}
fn subst_state_pos_rules<'a>(
    rules: Vec<AnnotatedRule<'a, ProcessAnnotation<LVar>>>,
    p_old: &[i64],
    p_new: &[i64],
) -> Vec<AnnotatedRule<'a, ProcessAnnotation<LVar>>> {
    rules
        .into_iter()
        .map(|mut r| {
            r.prems = r
                .prems
                .into_iter()
                .map(|f| subst_state_pos_fact(f, p_old, p_new))
                .collect();
            r
        })
        .collect()
}

#[test]
fn generated_rules_match_ordered_recursive_reference() {
    use tamarin_theory::sapic::SapicAction;
    fn build(seed: usize, depth: usize) -> Process<ProcessAnnotation<LVar>, SapicLVar> {
        let ann = ProcessAnnotation::empty();
        if depth == 0 {
            return Process::Null(ann);
        }
        let left = Box::new(build(seed / 6, depth - 1)).into();
        match seed % 6 {
            0 => Process::Action(SapicAction::Rep, ann, left),
            1 => Process::Action(
                SapicAction::ChOut {
                    chan: None,
                    msg: tamarin_term::lterm::pub_term("m"),
                },
                ann,
                left,
            ),
            2 => Process::Action(
                SapicAction::New(SapicLVar::untyped(LVar::new(
                    "x",
                    tamarin_term::lterm::LSort::Fresh,
                    depth as u64,
                ))),
                ann,
                left,
            ),
            5 => Process::Action(
                SapicAction::Lock(tamarin_term::lterm::pub_term("missing_annotation")),
                ann,
                left,
            ),
            n => Process::Comb(
                if n == 3 {
                    ProcessCombinator::Ndc
                } else {
                    ProcessCombinator::Parallel
                },
                ann,
                left,
                Box::new(build(seed / 7 + 1, depth - 1)).into(),
            ),
        }
    }
    let mut results = [0, 0];
    for seed in 0..500 {
        let process = build(seed, 4);
        for reliable in [false, true] {
            let mut ctx = super::tests::core_ctx();
            ctx.trans_reliable = reliable;
            let got = generate_rules(&ctx, &process, &vec![], &BTreeSet::new());
            let expected = generate_rules_reference(&ctx, &process, &vec![], &BTreeSet::new());
            results[usize::from(got.is_err())] += 1;
            assert_eq!(format!("{got:?}"), format!("{expected:?}"), "seed={seed}");
        }
    }
    assert!(results.iter().all(|count| *count > 0));
}

fn subst_state_pos_fact(f: TransFact, p_old: &[i64], p_new: &[i64]) -> TransFact {
    match f {
        TransFact::State(kind, pos, vs) if pos == p_old && !kind.is_semi_state() => {
            TransFact::State(StateKind::LState, p_new.to_vec(), vs)
        }
        other => other,
    }
}
