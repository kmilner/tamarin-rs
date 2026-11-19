//! Exercise specification-generated requests through the public backend. A fresh
//! native-only session isolates each request from earlier latched deferrals.
#![cfg(feature = "lean-unification")]
#![allow(clippy::disallowed_macros)] // Print the coverage report with --nocapture.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::process::Command;
use tamarin_term::algebra_backend::AlgebraBackend;
use tamarin_term::builtin::{fresh_var, hash, msg_var, zero_const};
use tamarin_term::function_symbols::AcSym;
use tamarin_term::lterm::{frees, pub_term, LNTerm, LVar, Name};
use tamarin_term::maude_proc::{MaudeError, MaudeHandle};
use tamarin_term::maude_sig::{hash_maude_sig, mset_maude_sig, xor_maude_sig};
use tamarin_term::rewriting::Equal;
use tamarin_term::subst::{apply_vterm, Subst};
use tamarin_term::term::{f_app_ac, f_app_list, Term};
use tamarin_term::vterm::Lit;

fn generated_requests() -> String {
    let lean = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean");
    let lake = std::env::var_os("TAMARIN_LAKE").unwrap_or_else(|| "lake".into());
    let run = |args: &[&str]| {
        let out = Command::new(&lake)
            .current_dir(&lean)
            .args(args)
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{args:?}\n{}\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8(out.stdout).unwrap()
    };
    run(&[
        "build",
        "Tamarin.ConstructorVariants",
        "Tamarin.MatchingFree",
        "Tamarin.SortCheck",
        "Tamarin.VariableElimination",
    ]);
    run(&[
        "env",
        "lean",
        "-DwarningAsError=true",
        "--run",
        "Tests/NativeCoverage.lean",
    ])
}

// Test-only postfix decoding. Rust smart constructors choose the AC representative.
fn term(text: &str, symbol: AcSym) -> LNTerm {
    let mut stack = Vec::new();
    for token in text.split('.') {
        let value = match token {
            "a" | "b" => pub_term(token),
            "z" => zero_const(),
            "h" => hash(stack.pop().unwrap()),
            "+" => {
                let r = stack.pop().unwrap();
                let l = stack.pop().unwrap();
                f_app_ac(symbol, vec![l, r])
            }
            _ if token.starts_with('f') => fresh_var("f", token[1..].parse().unwrap()),
            _ if token.starts_with('m') => msg_var("m", token[1..].parse().unwrap()),
            _ => panic!("unknown term token {token}"),
        };
        stack.push(value);
    }
    assert_eq!(stack.len(), 1, "{text}");
    stack.pop().unwrap()
}

// Accept any arm equivalent to identity on the observed variables, including
// independent, sort-preserving renamings in the arm's own witness scope.
fn covers_identity(query: &LNTerm, subst: &Subst<Name, LVar>) -> bool {
    let mut used = BTreeSet::new();
    frees(query).into_iter().all(|v| {
        let image = match subst.image_of(&v) {
            None => v,
            Some(Term::Lit(Lit::Var(w))) if w.sort == v.sort => *w,
            _ => return false,
        };
        used.insert(image)
    })
}

fn exercise(h: &MaudeHandle, op: &str, expected: &str, ts: &[LNTerm]) -> Result<(), MaudeError> {
    match (op, ts) {
        ("reduce", [t]) => {
            let result = h.reduce(t)?;
            match expected {
                "identity" => assert_eq!(&result, t),
                "probe" => {}
                _ => panic!("invalid reduction expectation {expected}"),
            }
        }
        ("variants", [_, ..]) => {
            let q = f_app_list(ts.to_vec());
            let arms = h.variants(&q)?;
            assert!(!arms.is_empty(), "empty variant family for {q:?}");
            match expected {
                "identity" => assert!(
                    arms.into_iter()
                        .any(|a| covers_identity(&q, &Subst::from_list(a))),
                    "{q:?}"
                ),
                "probe" => {}
                _ => panic!("invalid variant expectation {expected}"),
            }
        }
        ("unify" | "match", terms) => {
            let (pairs, tail) = terms.as_chunks::<2>();
            assert!(!pairs.is_empty() && tail.is_empty());
            let eqs: Vec<_> = pairs
                .iter()
                .map(|[pattern, subject]| {
                    // MaudeHandle takes (subject, pattern) for match_eqs.
                    let (l, r) = if op == "match" {
                        (subject, pattern)
                    } else {
                        (pattern, subject)
                    };
                    Equal {
                        lhs: l.clone(),
                        rhs: r.clone(),
                    }
                })
                .collect();
            let arms = if op == "unify" {
                h.unify(&eqs)?
            } else {
                let arms = h.match_eqs(&eqs)?;
                for arm in &arms {
                    let subst = Subst::from_list(arm.iter().cloned());
                    for e in &eqs {
                        assert_eq!(apply_vterm(&subst, e.rhs.clone()), e.lhs, "match {eqs:?}");
                    }
                }
                arms
            };
            match expected {
                "yes" | "no" => assert_eq!(!arms.is_empty(), expected == "yes", "{op} {eqs:?}"),
                "probe" => {}
                _ => panic!("invalid equation expectation {expected}"),
            }
        }
        _ => panic!("invalid request for {op}: {ts:?}"),
    }
    Ok(())
}

#[derive(Default)]
struct Coverage<'a> {
    required: usize,
    extra: usize,
    deferred: usize,
    smallest: Option<(usize, &'a str)>,
}

#[test]
fn public_backend_meets_generated_coverage_floor() {
    let cases = generated_requests();
    let mut report = BTreeMap::new();
    let plain = mset_maude_sig().merge(hash_maude_sig());
    let cancellation = xor_maude_sig().merge(hash_maude_sig());
    let presentation = |name: &str| match name {
        "ac" => (&plain, AcSym::Union),
        "xor" => (&cancellation, AcSym::Xor),
        _ => panic!("unknown theory {name}"),
    };
    for line in cases.lines() {
        let mut fields = line.split('\t');
        let theory = fields.next().unwrap();
        let op = fields.next().unwrap();
        let expected = fields.next().unwrap();
        let (sig, symbol) = presentation(theory);
        let ts: Vec<_> = fields.map(|e| term(e, symbol)).collect();
        let h = MaudeHandle::start_with_backend(
            "/nonexistent",
            sig.clone(),
            AlgebraBackend::NativeOnly,
        )
        .unwrap();
        let coverage = report.entry((theory, op)).or_insert_with(Coverage::default);
        match exercise(&h, op, expected, &ts) {
            Ok(()) => {
                h.check_backend_status().unwrap();
                if expected == "probe" {
                    coverage.extra += 1
                } else {
                    coverage.required += 1
                }
            }
            Err(MaudeError::UnsupportedOperation(_)) if expected == "probe" => {
                coverage.deferred += 1;
                let size = line.split('\t').skip(3).map(|t| t.split('.').count()).sum();
                let witness = (size, line);
                if coverage.smallest.is_none_or(|prev| witness < prev) {
                    coverage.smallest = Some(witness);
                }
            }
            Err(err) => panic!("{line}: {err}"),
        }
    }
    assert_eq!(report.len(), 8);
    for ((theory, op), c) in report {
        assert!(c.required > 0, "missing guaranteed {theory} {op} cases");
        println!(
            "{theory} {op}: {} required completed; exploratory {} completed, {} deferred",
            c.required, c.extra, c.deferred
        );
        if let Some((_, witness)) = c.smallest {
            let (sig, symbol) = presentation(theory);
            let ts: Vec<_> = witness
                .split('\t')
                .skip(3)
                .map(|s| term(s, symbol))
                .collect();
            let terms = ts
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ");
            println!("  smallest generated deferral: {op}({terms})");
            if let Ok(path) = std::env::var("MAUDE_PATH") {
                let oracle =
                    MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude)
                        .unwrap();
                exercise(&oracle, op, "probe", &ts).expect(witness);
                println!("  Maude completed this request");
            }
        }
    }
}
