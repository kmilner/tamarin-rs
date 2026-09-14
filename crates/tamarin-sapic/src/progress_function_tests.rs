use super::*;

#[test]
fn progress_distinguishes_parallel_choice_and_blocking_ndc() {
    use tamarin_theory::sapic::ProcessCombinator as PC;
    let ann = ProcessAnnotation::empty;
    for (comb, expected) in [
        (PC::Parallel, vec![vec![vec![1]], vec![vec![2]]]),
        (
            PC::CondEq(
                tamarin_term::vterm::const_term(tamarin_term::lterm::Name::new(
                    tamarin_term::lterm::NameTag::Pub,
                    "a",
                )),
                tamarin_term::vterm::const_term(tamarin_term::lterm::Name::new(
                    tamarin_term::lterm::NameTag::Pub,
                    "b",
                )),
            ),
            vec![vec![vec![1], vec![2]]],
        ),
        (PC::Ndc, vec![vec![vec![]]]),
    ] {
        let p = Process::Comb(
            comb,
            ann(),
            Box::new(Process::Null(ann())).into(),
            Box::new(Process::Null(ann())).into(),
        );
        let want = expected
            .into_iter()
            .map(|s| s.into_iter().collect())
            .collect();
        assert_eq!(f(&p), want);
    }
}

#[test]
fn progress_from_restores_paths_across_branches_and_ndc_jumps() {
    use tamarin_theory::sapic::ProcessCombinator as PC;
    fn reference(node: &AProc, parent_blocking: bool) -> PosSet {
        if matches!(node, Process::Null(_)) {
            return PosSet::new();
        }
        let blk = blocking(node);
        let mut result = PosSet::new();
        if !blk && parent_blocking {
            result.insert(Vec::new());
        }
        for pos in reference_next(node, false) {
            let child = process_at(node, &pos).unwrap();
            result.extend(prefix_set(&pos, &reference(child, blk)));
        }
        result
    }
    // Original recursive definition, restricted to small generated trees.
    fn reference_next(node: &AProc, include_null: bool) -> PosSet {
        match node {
            Process::Null(_) if include_null => [vec![]].into_iter().collect(),
            Process::Null(_) => PosSet::new(),
            Process::Action(..) => [vec![1]].into_iter().collect(),
            Process::Comb(comb, _, left, right) => {
                let mut out = PosSet::new();
                for (edge, child) in [(1, left), (2, right)] {
                    if matches!(comb, PC::Ndc) && blocking(child) {
                        out.extend(prefix_set(&[edge], &reference_next(child, include_null)));
                    } else {
                        out.insert(vec![edge]);
                    }
                }
                out
            }
        }
    }
    fn reference_to(node: &AProc) -> PosSetSet {
        if blocking(node) {
            return [[Vec::new()].into_iter().collect()].into_iter().collect();
        }
        if let Process::Comb(PC::Parallel, _, left, right) = node {
            let mut out = prefix_set_set(&[1], &reference_to(left));
            out.extend(prefix_set_set(&[2], &reference_to(right)));
            return out;
        }
        let mut out = [PosSet::new()].into_iter().collect();
        for pos in reference_next(node, true) {
            let child = process_at(node, &pos).unwrap();
            out = combine(&prefix_set_set(&pos, &reference_to(child)), &out);
        }
        out
    }
    fn output(body: AProc) -> AProc {
        Process::Action(
            SapicAction::ChOut {
                chan: None,
                msg: tamarin_term::lterm::pub_term("m"),
            },
            ProcessAnnotation::empty(),
            Box::new(body).into(),
        )
    }
    fn rep(body: AProc) -> AProc {
        Process::Action(
            SapicAction::Rep,
            ProcessAnnotation::empty(),
            Box::new(body).into(),
        )
    }
    fn branch(comb: PC<SapicLVar>, left: AProc, right: AProc) -> AProc {
        Process::Comb(
            comb,
            ProcessAnnotation::empty(),
            Box::new(left).into(),
            Box::new(right).into(),
        )
    }
    let null = || Process::Null(ProcessAnnotation::empty());
    let process = branch(
        PC::Parallel,
        branch(PC::Ndc, rep(rep(output(null()))), rep(output(null()))),
        rep(output(null())),
    );
    let expected = [vec![], vec![1, 1, 1, 1], vec![1, 2, 1], vec![2, 1]]
        .into_iter()
        .collect();
    assert_eq!(reference(&process, true), expected);
    assert_eq!(pf_from(&process), expected);

    fn generated(seed: &mut u64, depth: usize) -> AProc {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        let choice = (*seed >> 32) % 6;
        if depth == 0 || choice == 0 {
            return Process::Null(ProcessAnnotation::empty());
        }
        let left = generated(seed, depth - 1);
        match choice {
            1 => rep(left),
            2 => output(left),
            _ => branch(
                match choice {
                    3 => PC::Ndc,
                    4 => PC::Parallel,
                    _ => PC::CondEq(
                        tamarin_term::lterm::pub_term("a"),
                        tamarin_term::lterm::pub_term("b"),
                    ),
                },
                left,
                generated(seed, depth - 1),
            ),
        }
    }
    let mut seed = 27321;
    for _ in 0..256 {
        let process = generated(&mut seed, 7);
        assert_eq!(pf_from(&process), reference(&process, true));
        assert_eq!(f(&process), reference_to(&process));
        assert_eq!(Blocking::new(&process).get(&process), blocking(&process));
        for include_null in [false, true] {
            let nodes = next_processes(&process, include_null, &mut Blocking::new(&process));
            assert_eq!(
                nodes.iter().map(|(pos, _)| pos.clone()).collect::<Vec<_>>(),
                reference_next(&process, include_null)
                    .into_iter()
                    .collect::<Vec<_>>()
            );
            for (pos, node) in nodes {
                assert!(std::ptr::eq(node, process_at(&process, &pos).unwrap()));
            }
        }
        // Original sorted relation: the least source for each target wins.
        let mut relation = BTreeSet::new();
        for from in reference(&process, true) {
            for tos in prefix_set_set(&from, &reference_to(process_at(&process, &from).unwrap())) {
                relation.extend(tos.into_iter().map(|to| (to, from.clone())));
            }
        }
        let inverse = pf_inv(&process).unwrap();
        for (to, _) in &relation {
            let expected = relation
                .iter()
                .find(|(target, _)| target == to)
                .unwrap()
                .1
                .clone();
            assert_eq!(inverse(to), Some(expected));
        }
        assert_eq!(inverse(&[3]), None);
        assert_eq!(pf(&process, &[3]).unwrap_err(), "pf: invalid position [3]");
    }
}

#[test]
fn deep_progress_preserves_blocking_and_absolute_positions() {
    tamarin_test_support::on_stack(256 * 1024, || {
        for choice in [true, false] {
            let mut p = Process::Null(ProcessAnnotation::empty());
            for _ in 0..8192 {
                p = if choice {
                    Process::Comb(
                        tamarin_theory::sapic::ProcessCombinator::Ndc,
                        ProcessAnnotation::empty(),
                        Box::new(p).into(),
                        Box::new(Process::Null(ProcessAnnotation::empty())).into(),
                    )
                } else {
                    Process::Action(
                        SapicAction::ChOut {
                            chan: None,
                            msg: tamarin_term::lterm::pub_term("m"),
                        },
                        ProcessAnnotation::empty(),
                        Box::new(p).into(),
                    )
                };
            }
            let froms = if choice {
                PosSet::new()
            } else {
                [vec![]].into()
            };
            let target = if choice { vec![] } else { vec![1; 8192] };
            assert_eq!(pf_from(&p), froms, "choice={choice}");
            assert_eq!(f(&p), [[target].into()].into(), "choice={choice}");
            assert!(pf_inv(&p).is_ok(), "choice={choice}");
            if !choice {
                for _ in 0..8192 {
                    p = Process::Action(
                        SapicAction::Rep,
                        ProcessAnnotation::empty(),
                        Box::new(p).into(),
                    );
                }
                let inv = pf_inv(&p).unwrap();
                assert_eq!(inv(&vec![1; 16384]), Some(vec![1; 8192]));
            }
        }
    });
}
