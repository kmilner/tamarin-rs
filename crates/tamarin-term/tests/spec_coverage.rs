//! Exercise specification-generated requests through the public backend. A fresh
//! native-only session isolates each request from earlier latched deferrals.
#![cfg(feature = "lean-unification")]
#![allow(clippy::disallowed_macros)] // Print the coverage report with --nocapture.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::process::Command;
use tamarin_term::algebra_backend::AlgebraBackend;
use tamarin_term::builtin::{
    bp_rules, dh_neutral, emap, exp, fresh_var, fst, hash, inv, msg_var, one_const, pair, pmult,
    pub_var, snd, zero_const,
};
use tamarin_term::function_symbols::{
    nat_one_sym, AcFctSym, AcSym, Constructability, NdcState, NoEqSym, Privacy,
};
use tamarin_term::lterm::{frees, pub_term, HasFrees, LNTerm, LSort, LVar, Name};
use tamarin_term::maude_proc::{MaudeError, MaudeHandle};
use tamarin_term::maude_sig::{
    bp_maude_sig, dh_maude_sig, hash_maude_sig, mset_maude_sig, nat_maude_sig, pair_maude_sig,
    xor_maude_sig, MaudeSig,
};
use tamarin_term::rewriting::{Equal, RRule};
use tamarin_term::subst::{apply_vterm, Subst};
use tamarin_term::subterm_rule::rrule_to_ctxt_st_rule;
use tamarin_term::term::{f_app_ac, f_app_list, f_app_no_eq, Term};
use tamarin_term::vterm::Lit;

fn generated_requests() -> String {
    let lean = Path::new(env!("TAMARIN_ALGEBRA_LEAN_DIR"));
    let lake = std::env::var_os("TAMARIN_LAKE").unwrap_or_else(|| "lake".into());
    let run = |args: &[&str]| {
        let out = Command::new(&lake)
            .current_dir(lean)
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
        "Tamarin.Cancellation",
        "Tamarin.ConstructorReduction",
        "Tamarin.DHPeer",
        "Tamarin.MatchingFree",
        "Tamarin.SortCheck",
        "Tamarin.VariablePermutation",
    ]);
    run(&[
        "env",
        "lean",
        "-DwarningAsError=true",
        "--run",
        "Tests/NativeCoverage.lean",
    ])
}

// These nullary constructors deliberately share the spelling of public names.
fn marker(name: &'static [u8]) -> NoEqSym {
    NoEqSym::new(name, 0, Privacy::Public, Constructability::Constructor)
}

fn marker_presentation(cases: &str) -> (MaudeSig, AcSym) {
    let f = AcFctSym::new(
        b"merge",
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    let symbol = AcSym::AcFct(f);
    let mut sig = hash_maude_sig();
    sig.st_ac_fun_syms.insert(f);
    sig.st_fun_syms.extend([marker(b"a"), marker(b"b")]);
    for line in cases.lines() {
        if let Some(sides) = line.strip_prefix("markers\trule\toriented\t") {
            let (lhs, rhs) = sides.split_once('\t').unwrap();
            let rule = RRule::new(term(lhs, symbol), term(rhs, symbol));
            sig.st_rules.insert(rrule_to_ctxt_st_rule(&rule).unwrap());
        }
    }
    assert_eq!(sig.st_rules.len(), 2);
    (sig.refresh(), symbol)
}

// Test-only postfix decoding. Rust smart constructors choose the AC representative.
fn term(text: &str, symbol: AcSym) -> LNTerm {
    let mut stack = Vec::new();
    for token in text.split('.') {
        let value = match token {
            "a" | "b" => pub_term(token),
            "R" => f_app_no_eq(marker(b"a"), vec![]),
            "B" => f_app_no_eq(marker(b"b"), vec![]),
            "z" => zero_const(),
            "one" => one_const(),
            "nat1" => f_app_no_eq(nat_one_sym(), vec![]),
            "neutral" => dh_neutral(),
            "inv" => inv(stack.pop().unwrap()),
            "pow" | "pmult" | "emap" => {
                let right = stack.pop().unwrap();
                let left = stack.pop().unwrap();
                match token {
                    "pow" => exp(left, right),
                    "pmult" => pmult(left, right),
                    _ => emap(left, right),
                }
            }
            "h" => hash(stack.pop().unwrap()),
            "l" => fst(stack.pop().unwrap()),
            "r" => snd(stack.pop().unwrap()),
            "p" => {
                let right = stack.pop().unwrap();
                pair(stack.pop().unwrap(), right)
            }
            "+" => {
                let r = stack.pop().unwrap();
                let l = stack.pop().unwrap();
                f_app_ac(symbol, vec![l, r])
            }
            _ if token.starts_with('f') => fresh_var("f", token[1..].parse().unwrap()),
            _ if token.starts_with('u') => pub_var("u", token[1..].parse().unwrap()),
            _ if token.starts_with('m') => msg_var("m", token[1..].parse().unwrap()),
            _ if token.starts_with('n') => Term::Lit(Lit::Var(LVar::new(
                "n",
                LSort::Nat,
                token[1..].parse().unwrap(),
            ))),
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

type Answers = Vec<Vec<(LVar, LNTerm)>>;

// Column order fixes caller identity. Use one witness renaming across every
// input image and observed value, including both sides of a commutative head.
fn canonical_row(columns: &[LNTerm]) -> LNTerm {
    let row = f_app_list(columns.to_vec());
    // Only witnesses with identical sort and occurrence counts in every
    // column can exchange canonical positions. This also handles repeated
    // variables in a single commutative subterm.
    let fingerprint = |v: &LVar| {
        let counts: Vec<_> = columns
            .iter()
            .map(|t| {
                let mut count = 0usize;
                t.for_each_free(&mut |w| count += usize::from(w == v));
                count
            })
            .collect();
        (v.sort, counts)
    };
    let mut names = frees(&row);
    names.sort_by_cached_key(&fingerprint);
    let classes: Vec<_> = names.iter().map(fingerprint).collect();
    fn visit(
        row: &LNTerm,
        names: &mut [LVar],
        ends: &[usize],
        pos: usize,
        best: &mut Option<LNTerm>,
    ) {
        if pos == names.len() {
            let value = row.clone().map_free(&mut |v| {
                LVar::new(
                    "w",
                    v.sort,
                    names.iter().position(|w| *w == v).unwrap() as u64,
                )
            });
            if best.as_ref().is_none_or(|current| value < *current) {
                *best = Some(value);
            }
        } else {
            for i in pos..ends[pos] {
                names.swap(i, pos);
                visit(row, names, ends, pos + 1, best);
                names.swap(i, pos);
            }
        }
    }
    let ends = (0..classes.len())
        .map(|i| classes.partition_point(|c| c <= &classes[i]))
        .collect::<Vec<_>>();
    let mut best = None;
    visit(&row, &mut names, &ends, 0, &mut best);
    best.unwrap()
}

fn valued_rows(h: &MaudeHandle, op: &str, ts: &[LNTerm], arms: Answers) -> Vec<LNTerm> {
    let keys = frees(&f_app_list(ts.to_vec()));
    let mut rows: Vec<_> = arms
        .into_iter()
        .map(|arm| {
            let subst = Subst::from_list(arm);
            let mut columns: Vec<_> = keys
                .iter()
                .map(|key| {
                    let image = apply_vterm(&subst, Term::Lit(Lit::Var(*key)));
                    if op == "variants" {
                        assert_eq!(h.reduce(&image).unwrap(), image, "reducible image of {key}");
                    }
                    image
                })
                .collect();
            if op == "variants" {
                for t in ts {
                    columns.push(h.reduce(&apply_vterm(&subst, t.clone())).unwrap());
                }
            }
            canonical_row(&columns)
        })
        .collect();
    rows.sort();
    rows
}

fn exercise(
    h: &MaudeHandle,
    op: &str,
    expected: &str,
    ts: &[LNTerm],
) -> Result<Answers, MaudeError> {
    match (op, ts) {
        ("reduce", [t, nf]) if expected == "exact" => {
            assert_eq!(&h.reduce(t)?, nf, "{t}");
            assert_eq!(h.reduce(&hash(t.clone()))?, hash(nf.clone()), "hash({t})");
        }
        ("reduce", [t]) => {
            let result = h.reduce(t)?;
            match expected {
                "identity" => assert_eq!(&result, t),
                "complete" => assert_eq!(h.reduce(&result).unwrap(), result, "{t}"),
                "probe" => {}
                _ => panic!("invalid reduction expectation {expected}"),
            }
            // In the generated signatures hash is absent from every rule head.
            // Each supported child must therefore also be supported under hash.
            let wrapped = hash(t.clone());
            assert_eq!(
                h.reduce(&wrapped)
                    .unwrap_or_else(|err| panic!("{wrapped}: {err}")),
                hash(result),
                "{wrapped}"
            );
        }
        ("variants", [_, ..]) => {
            let q = f_app_list(ts.to_vec());
            let arms = h.variants(&q)?;
            assert!(!arms.is_empty(), "empty variant family for {q:?}");
            let visible = frees(&q);
            assert!(
                arms.iter().flatten().all(|(v, _)| visible.contains(v)),
                "{q:?}"
            );
            match expected {
                "identity" | "identity-only" => {
                    if expected == "identity-only" {
                        assert_eq!(arms.len(), 1, "{q}");
                    }
                    assert!(
                        arms.iter()
                            .any(|a| covers_identity(&q, &Subst::from_list(a.iter().cloned()))),
                        "{q:?}"
                    );
                }
                count if count.starts_with("rows=") => {
                    assert_eq!(arms.len(), count[5..].parse::<usize>().unwrap(), "{q}");
                }
                "complete" | "probe" => {}
                _ => panic!("invalid variant expectation {expected}"),
            }
            return Ok(arms);
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
                let pattern_keys: BTreeSet<_> = pairs.iter().flat_map(|[p, _]| frees(p)).collect();
                for arm in &arms {
                    assert!(
                        arm.iter().all(|(v, _)| pattern_keys.contains(v)),
                        "unexpected match key: {eqs:?}"
                    );
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
                count if count.starts_with("rows=") => {
                    // Matching keeps every subject rigid. Ground-sided
                    // unification has the same exact caller-image interpretation.
                    let keys = frees(&f_app_list(pairs.iter().map(|[p, _]| p.clone()).collect()));
                    let mut distinct = BTreeSet::new();
                    for arm in &arms {
                        let subst = Subst::from_list(arm.iter().cloned());
                        for [pattern, subject] in pairs {
                            assert!(op == "match" || frees(subject).is_empty());
                            assert_eq!(
                                apply_vterm(&subst, pattern.clone()),
                                *subject,
                                "{op} {eqs:?}"
                            );
                        }
                        let images: Vec<_> = keys
                            .iter()
                            .map(|key| apply_vterm(&subst, Term::Lit(Lit::Var(*key))))
                            .collect();
                        assert!(distinct.insert(images), "duplicate {op} answer for {eqs:?}");
                    }
                    assert_eq!(
                        arms.len(),
                        count[5..].parse::<usize>().unwrap(),
                        "{op} {eqs:?}"
                    );
                }
                _ => panic!("invalid equation expectation {expected}"),
            }
            return Ok(arms);
        }
        _ => panic!("invalid request for {op}: {ts:?}"),
    }
    Ok(vec![])
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
    let bp = bp_maude_sig().merge(hash_maude_sig());
    let rules: BTreeSet<_> = cases
        .lines()
        .filter_map(|line| line.strip_prefix("bp\trule\toriented\t"))
        .map(|sides| {
            let (lhs, rhs) = sides.split_once('\t').unwrap();
            let schema =
                |text| term(text, AcSym::Mult).map_free(&mut |v| LVar::new("x", v.sort, v.idx));
            RRule::new(schema(lhs), schema(rhs))
        })
        .collect();
    assert_eq!(
        rules,
        bp_rules(),
        "generated pairing schemas must track Tamarin's rule table"
    );
    assert!(rules.is_subset(&bp.rrules()));
    let dh = dh_maude_sig().merge(hash_maude_sig());
    let plain = mset_maude_sig().merge(hash_maude_sig());
    let nat = nat_maude_sig().merge(hash_maude_sig());
    assert!(
        nat.rrules().is_empty(),
        "generated Nat cases assume constructor-only addition and one"
    );
    let cancellation = xor_maude_sig().merge(hash_maude_sig());
    let mixed = cancellation.clone().merge(pair_maude_sig());
    let (markers, merge) = marker_presentation(&cases);
    let maude_path = tamarin_test_support::configured_maude_path();
    // Generated requests are grouped by theory. Keep only the current
    // presentation's reference process alive throughout that block.
    let mut active_oracle: Option<(&str, MaudeHandle)> = None;
    let presentation = |name: &str| match name {
        "bp" => (&bp, AcSym::Mult),
        "dh" => (&dh, AcSym::Mult),
        "ac" => (&plain, AcSym::Union),
        "nat" => (&nat, AcSym::NatPlus),
        "xor" => (&cancellation, AcSym::Xor),
        "xor-pair" => (&mixed, AcSym::Xor),
        "markers" => (&markers, merge),
        _ => panic!("unknown theory {name}"),
    };
    for line in cases.lines() {
        let mut fields = line.split('\t');
        let theory = fields.next().unwrap();
        let op = fields.next().unwrap();
        let expected = fields.next().unwrap();
        if matches!(
            (theory, op, expected),
            ("markers" | "bp", "rule", "oriented")
        ) {
            continue;
        }
        let (sig, symbol) = presentation(theory);
        let ts: Vec<_> = fields.map(|e| term(e, symbol)).collect();
        // Every ordinary unification and matching query is a representable input to
        // the total fallback, even when no particular answer count is specified.
        let exploratory = !matches!(op, "unify" | "match")
            && (expected == "probe" || expected.starts_with("probe-"));
        let check = expected.strip_prefix("probe-").unwrap_or(expected);
        let compare = matches!(theory, "bp" | "nat")
            || theory == "dh" && (op == "variants" || (op, check) == ("reduce", "exact"))
            || theory == "markers" && (op, check) == ("reduce", "exact");
        let reference = if let Some(path) = maude_path.as_ref().filter(|_| compare) {
            if active_oracle
                .as_ref()
                .is_none_or(|(name, _)| *name != theory)
            {
                drop(active_oracle.take());
                active_oracle = Some((
                    theory,
                    MaudeHandle::start_with_backend(path, sig.clone(), AlgebraBackend::Maude)
                        .unwrap(),
                ));
            }
            let oracle = &active_oracle.as_ref().unwrap().1;
            Some((oracle, exercise(oracle, op, check, &ts).expect(line)))
        } else {
            None
        };
        let h = MaudeHandle::start_with_backend(
            "/nonexistent",
            sig.clone(),
            AlgebraBackend::NativeOnly,
        )
        .unwrap();
        let coverage = report.entry((theory, op)).or_insert_with(Coverage::default);
        match exercise(&h, op, check, &ts) {
            Ok(arms) => {
                if matches!(theory, "bp" | "nat")
                    && op != "reduce"
                    && let Some((oracle, oracle_arms)) = reference
                {
                    assert_eq!(
                        valued_rows(&h, op, &ts, arms),
                        valued_rows(oracle, op, &ts, oracle_arms),
                        "{line}"
                    );
                }
                h.check_backend_status().unwrap();
                if exploratory {
                    coverage.extra += 1
                } else {
                    coverage.required += 1
                }
            }
            Err(MaudeError::UnsupportedOperation(_)) if exploratory => {
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
    drop(active_oracle);
    assert_eq!(report.len(), 24);
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
            if let Some(path) = tamarin_test_support::configured_maude_path() {
                let oracle =
                    MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude)
                        .unwrap();
                let expected = witness.split('\t').nth(2).unwrap();
                exercise(
                    &oracle,
                    op,
                    expected.strip_prefix("probe-").unwrap_or(expected),
                    &ts,
                )
                .expect(witness);
                println!("  Maude completed this request");
            }
        }
    }
}
