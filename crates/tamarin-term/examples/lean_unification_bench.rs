//! Compare the integrated Lean path with the existing memoized Maude path.
#![allow(clippy::disallowed_macros)]

use std::hint::black_box;
use std::time::{Duration, Instant};

use tamarin_term::function_symbols::AcSym;
use tamarin_term::lterm::{pub_term, LNTerm, LSort, LVar};
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::maude_sig::mset_maude_sig;
use tamarin_term::rewriting::Equal;
use tamarin_term::term::{f_app_ac, Term};
use tamarin_term::vterm::Lit;

type Answers = Vec<Vec<(LVar, LNTerm)>>;

fn run(
    handle: &MaudeHandle,
    queries: &[Vec<Equal<LNTerm>>],
    lean: bool,
) -> (Duration, Vec<Answers>) {
    let start = Instant::now();
    let answers = queries
        .iter()
        .map(|eqs| {
            if lean {
                handle.unify(black_box(eqs))
            } else {
                handle.unify_via_maude(black_box(eqs))
            }
            .expect("unification failed")
        })
        .collect();
    (start.elapsed(), answers)
}

fn main() {
    assert!(
        std::env::var_os("TAM_RS_VERIFY_LEAN_UNIFY").is_none(),
        "unset TAM_RS_VERIFY_LEAN_UNIFY when benchmarking"
    );
    assert!(
        std::env::var_os("TAM_RS_NO_LEAN_UNIFY").is_none(),
        "unset TAM_RS_NO_LEAN_UNIFY when benchmarking"
    );
    let count = std::env::args()
        .nth(1)
        .map(|text| text.parse::<usize>().expect("query count"))
        .unwrap_or(1000);
    assert!((1..=4096).contains(&count), "query count must be 1..=4096");
    let maude_path = tamarin_test_support::maude_path().unwrap_or_else(|| "maude".into());
    println!(
        "workload,cache,queries,lean_us_per_query,maude_us_per_query,speedup,lean_completions"
    );
    for workload in ["ground_equal", "ground_unequal", "one_variable"] {
        let queries: Vec<_> = (0..count)
            .map(|i| {
                // Constant names are renumbered in Maude's wire format, so
                // unique names alone still hit the reply cache. Six positive
                // base-four multiplicities give 4096 distinct wire shapes.
                let mut digits = i;
                let mut atoms = Vec::new();
                for atom in 0..6 {
                    let multiplicity = 1 + digits % 4;
                    digits /= 4;
                    atoms.extend(std::iter::repeat_n(
                        pub_term(format!("a{atom}")),
                        multiplicity,
                    ));
                }
                let (lhs, rhs) = match workload {
                    "ground_equal" => {
                        let t = f_app_ac(AcSym::Union, atoms);
                        (t.clone(), t)
                    }
                    "ground_unequal" => {
                        let lhs = f_app_ac(AcSym::Union, atoms.clone());
                        atoms.push(pub_term("a0"));
                        (lhs, f_app_ac(AcSym::Union, atoms))
                    }
                    _ => {
                        let mut pattern = atoms.clone();
                        pattern.push(Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 0))));
                        atoms.extend([pub_term("extra-a"), pub_term("extra-b")]);
                        (
                            f_app_ac(AcSym::Union, pattern),
                            f_app_ac(AcSym::Union, atoms),
                        )
                    }
                };
                vec![Equal { lhs, rhs }]
            })
            .collect();
        let lean = MaudeHandle::start(&maude_path, mset_maude_sig()).expect("Lean dispatch handle");
        let oracle =
            MaudeHandle::start(&maude_path, mset_maude_sig()).expect("Maude oracle handle");
        // Initialize the Lean runtime before timing. Inputs and process startup
        // are outside the measurement; each cold query has a unique wire shape.
        let warm = [Equal {
            lhs: f_app_ac(AcSym::Union, vec![pub_term("warm-a"), pub_term("warm-b")]),
            rhs: f_app_ac(AcSym::Union, vec![pub_term("warm-b"), pub_term("warm-a")]),
        }];
        lean.unify(&warm).unwrap();
        for cache in ["cold", "warm"] {
            let before = lean.stats().lean_unify_count;
            let maude_before = oracle.stats().unify_count;
            // Alternate order so process scheduling does not always favor one path.
            let ((lean_time, lean_answers), (maude_time, maude_answers)) = if cache == "cold" {
                (run(&lean, &queries, true), run(&oracle, &queries, false))
            } else {
                let maude_result = run(&oracle, &queries, false);
                (run(&lean, &queries, true), maude_result)
            };
            assert_eq!(
                lean_answers, maude_answers,
                "{workload}/{cache} answers differ"
            );
            let completed = lean.stats().lean_unify_count - before;
            assert_eq!(completed, count as u64, "workload fell back to Maude");
            let maude_calls = oracle.stats().unify_count - maude_before;
            assert_eq!(
                maude_calls,
                if cache == "cold" { count as u64 } else { 0 },
                "unexpected Maude reply-cache behavior"
            );
            println!(
                "{workload},{cache},{count},{:.3},{:.3},{:.2},{completed}",
                lean_time.as_secs_f64() * 1e6 / count as f64,
                maude_time.as_secs_f64() * 1e6 / count as f64,
                maude_time.as_secs_f64() / lean_time.as_secs_f64()
            );
        }
    }
}
