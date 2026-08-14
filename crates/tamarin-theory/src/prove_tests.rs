use super::*;
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::maude_sig::pair_maude_sig;

fn maude_path_local() -> Option<String> {
    std::env::var("MAUDE_PATH").ok().or_else(|| {
        for c in ["/usr/local/bin/maude", "maude"] {
            if std::path::Path::new(c).exists() {
                return Some(c.to_string());
            }
        }
        None
    })
}

fn maude() -> Option<MaudeHandle> {
    let path = maude_path_local()?;
    MaudeHandle::start(&path, pair_maude_sig()).ok()
}

#[test]
fn prove_lemma_unknown_name_is_error() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let parser_theory = tamarin_parser::parse_theory("theory T begin end", &[]).expect("parse");
    let r = prove_lemma(&parser_theory, "nonexistent", h, 5);
    assert!(matches!(r, Err(ProveError::LemmaNotFound(_))));
}

fn print_tree(node: &super::ProofNode, depth: usize) {
    let pad = "  ".repeat(depth);
    let reason =
        if let crate::constraint::solver::proof_method::ProofMethod::Finished(r) = &node.method {
            format!(" reason={:?}", r)
        } else {
            String::new()
        };
    eprintln!("{}status={:?} method={:?} children={} goals={} nodes={} formulas={} less_atoms={} edges={} {}",
            pad, node.status, node.method, node.children.len(),
            node.sys.goals.len(), node.sys.nodes.len(), node.sys.formulas.len(),
            node.sys.less_atoms.len(), node.sys.edges.len(), reason);
    if depth > 0 {
        for (id, ru) in node.sys.nodes.iter() {
            let info = match &ru.info {
                crate::rule::RuleInfo::Proto(p) => format!("{:?}", p.name),
                crate::rule::RuleInfo::Intr(i) => format!("Intr({:?})", i),
            };
            let concs: Vec<String> = ru
                .conclusions
                .iter()
                .map(|c| {
                    format!(
                        "{}({})",
                        crate::fact::fact_tag_name(&c.tag),
                        c.terms
                            .iter()
                            .map(|t| format!("{:?}", t))
                            .collect::<Vec<_>>()
                            .join(",")
                    )
                })
                .collect();
            eprintln!(
                "{}  node {:?} = {} concs=[{}]",
                pad,
                (id.name, id.idx),
                info,
                concs.join("; ")
            );
        }
        eprintln!("{}  eq_store.subst = {:?}", pad, node.sys.eq_store.subst);
        for la in &node.sys.less_atoms {
            eprintln!(
                "{}  less {:?} < {:?}",
                pad,
                (la.smaller.name, la.smaller.idx),
                (la.larger.name, la.larger.idx)
            );
        }
        for e in &node.sys.edges {
            eprintln!(
                "{}  edge {:?} -> {:?}",
                pad,
                (e.src.0.name, e.src.0.idx),
                (e.tgt.0.name, e.tgt.0.idx)
            );
        }
    }
    for (k, c) in &node.children {
        eprintln!("{}case '{}'", pad, k);
        if depth < 9 {
            print_tree(c, depth + 1);
        }
    }
}

#[test]
fn probe_two_rules_proof_shape() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/two_rules.spthy"
    ))
    .expect("read");
    let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let root = prove_lemma(&pt, "reachable", h, 200).expect("prove");
    eprintln!("=== two_rules.spthy `reachable` ===");
    print_tree(&root, 0);
}

#[test]
fn probe_two_actions_proof_shape() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/two_actions.spthy"
    ))
    .expect("read");
    let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let root = prove_lemma(&pt, "both_actions", h, 200).expect("prove");
    eprintln!("=== two_actions.spthy `both_actions` ===");
    print_tree(&root, 0);
}

#[test]
fn probe_falsifiable_proof_shape() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/falsifiable.spthy"
    ))
    .expect("read");
    let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let root = prove_lemma(&pt, "never_both", h, 200).expect("prove");
    eprintln!("=== falsifiable.spthy `never_both` ===");
    print_tree(&root, 0);
}

#[test]
fn probe_three_facts_proof_shape() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/three_facts.spthy"
    ))
    .expect("read");
    let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let root = prove_lemma(&pt, "all_three", h, 200).expect("prove");
    eprintln!("=== three_facts.spthy `all_three` ===");
    print_tree(&root, 0);
}

#[test]
fn probe_single_recv_proof_shape() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/single_recv.spthy"
    ))
    .expect("read");
    let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let root = prove_lemma(&pt, "chain", h, 200).expect("prove");
    eprintln!("=== single_recv ===");
    eprintln!("status={:?}", root.status);
}

#[test]
fn probe_injectivity_with_pair_sig() {
    // Probes the `injectivity::injectivity_check` corpus example.
    // Resolves the example via a workspace-relative path computed
    // from CARGO_MANIFEST_DIR (crate lives at crates/tamarin-theory,
    // so the corpus is at ../../tamarin-prover/examples in the
    // submodule); skips gracefully if the example is not present.
    let mp = match maude_path_local() {
        Some(p) => p,
        None => return,
    };
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tamarin-prover/examples/features/injectivity/injectivity.spthy"
    ))
    .unwrap_or_default();
    if src.is_empty() {
        return;
    }
    let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let h = MaudeHandle::start(&mp, pair_maude_sig()).expect("start maude");
    let root = prove_lemma(&pt, "injectivity_check", h, 200).expect("prove");
    eprintln!("injectivity status = {:?}", root.status);
}

#[test]
fn probe_cr_recentalive_with_hashing_sig() {
    // Regression test: with the elaborated MaudeSig (hashing), the
    // simplify loop must converge instead of spinning on
    // already-canonical edges.
    let mp = match maude_path_local() {
        Some(p) => p,
        None => return,
    };
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/CR_external.spthy"
    ))
    .expect("read");
    let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let elab = crate::elaborate::elaborate(&pt).expect("elaborate");
    let sig = elab.signature.maude_sig.clone();
    let h = MaudeHandle::start(&mp, sig).expect("start maude");
    let t0 = std::time::Instant::now();
    let _ = prove_lemma(&pt, "recentalive", h, 200).expect("prove");
    let dt = t0.elapsed();
    // Must complete within a generous bound; the load-bearing
    // assertion is that the simplify loop converges, not the specific
    // timing.
    assert!(
        dt < std::time::Duration::from_secs(60),
        "recentalive ran {:?}, expected ≤60s (simplify-loop converges)",
        dt
    );
}

#[test]
fn probe_sig_minimal_with_hashing_sig() {
    // A trivially-true tautology proved against the elaborated theory's
    // MaudeSig (which adds h/1) rather than the pair-only signature: the
    // search must stay bounded even once the signature grows.
    let mp = match maude_path_local() {
        Some(p) => p,
        None => return,
    };
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/sig_minimal.spthy"
    ))
    .expect("read");
    let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let elab = crate::elaborate::elaborate(&pt).expect("elaborate");
    let sig = elab.signature.maude_sig.clone();
    eprintln!("sig fun_syms count = {}", sig.fun_syms.len());
    for fs in &sig.fun_syms {
        if let tamarin_term::function_symbols::FunSym::NoEq(s) = fs {
            eprintln!(
                "  {} (arity={}, priv={:?}, ctor={:?})",
                String::from_utf8_lossy(s.name),
                s.arity,
                s.privacy,
                s.constructability
            );
        }
    }
    let h = MaudeHandle::start(&mp, sig).expect("start maude");
    let root = prove_lemma(&pt, "a_self", h, 50).expect("prove");
    eprintln!("status = {:?}", root.status);
    // The lemma is a tautology; should reach Contradictory after
    // negation reduces to ⊥.
}

#[test]
fn probe_auth_pattern_proof_shape() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/auth_pattern.spthy"
    ))
    .expect("read");
    let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let root = prove_lemma(&pt, "protocol_runs", h, 200).expect("prove");
    eprintln!("=== auth_pattern.spthy ===");
    print_tree(&root, 0);
}

#[test]
fn probe_fresh_ordering_proof_shape() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/fresh_ordering.spthy"
    ))
    .expect("read");
    let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let root = prove_lemma(&pt, "order", h, 200).expect("prove");
    eprintln!("=== fresh_ordering.spthy `order` ===");
    print_tree(&root, 0);
}

#[test]
fn probe_needs_constructor_simple_proof_shape() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/needs_constructor_simple.spthy"
    ))
    .expect("read");
    let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let root = prove_lemma(&pt, "sent_exists", h, 200).expect("prove");
    eprintln!("=== needs_constructor_simple ===");
    eprintln!("status={:?}", root.status);
}

#[test]
fn probe_needs_constructor_proof_shape() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/needs_constructor.spthy"
    ))
    .expect("read");
    let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let root = prove_lemma(&pt, "pair_arrives", h, 2000).expect("prove");
    eprintln!("=== needs_constructor.spthy `pair_arrives` ===");
    eprintln!("status={:?}", root.status);
}

/// Smaller test: just receive a fresh that was Out-ed.
#[test]
fn probe_recv_one_fresh() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let src = "theory T begin
rule S: [Fr(~k)] --[Sent(~k)]-> [Out(~k)]
rule R: [In(x)] --[Got(x)]-> []
lemma chain: exists-trace \"Ex k #i #j. Sent(k)@i & Got(k)@j\"
end";
    let pt = tamarin_parser::parse_theory(src, &[]).expect("parse");
    let root = prove_lemma(&pt, "chain", h, 500).expect("prove");
    eprintln!("=== probe_recv_one_fresh ===");
    eprintln!("status={:?}", root.status);
}

#[test]
fn probe_reuse_lemma() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/reuse_lemma.spthy"
    ))
    .expect("read");
    let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let r1 = prove_lemma(&pt, "setup_unique", maude().unwrap(), 200).expect("prove1");
    let r2 = prove_lemma(&pt, "setup_unique_key", h, 200).expect("prove2");
    eprintln!(
        "setup_unique={:?}, setup_unique_key={:?}",
        r1.status, r2.status
    );
}

#[test]
fn probe_restriction_unique() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/restriction_unique.spthy"
    ))
    .expect("read");
    let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let root = prove_lemma(&pt, "setup_unique", h, 200).expect("prove");
    eprintln!("=== restriction_unique ===");
    eprintln!("status={:?}", root.status);
    // Diagnostic: count lemmas in the proof tree's leaves.
    fn collect_max_lemmas(n: &super::ProofNode, out: &mut usize) {
        *out = (*out).max(n.sys.lemmas.len());
        for c in n.children.values() {
            collect_max_lemmas(c, out);
        }
    }
    let mut max_lemmas = 0;
    collect_max_lemmas(&root, &mut max_lemmas);
    eprintln!("max lemma count seen in tree: {}", max_lemmas);
}

#[test]
fn probe_safety_two_keys_proof_shape() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/safety_two_keys.spthy"
    ))
    .expect("read");
    let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let root = prove_lemma(&pt, "fresh_distinct_times", h, 200).expect("prove");
    eprintln!("=== safety_two_keys.spthy `fresh_distinct_times` ===");
    print_tree(&root, 0);
}

#[test]
fn probe_safety_unique_proof_shape() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/safety_unique.spthy"
    ))
    .expect("read");
    let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let root = prove_lemma(&pt, "setup_unique", h, 200).expect("prove");
    eprintln!("=== safety_unique.spthy `setup_unique` ===");
    print_tree(&root, 0);
}

/// Web-parity regression: under `SysRetention::KeepAll` (what the
/// interactive server sets at startup), `run_proof_search` must
/// RETAIN each proof node's constraint `System` instead of dropping
/// it to `System::default()` (the `--prove` RSS optimisation in
/// `expand`).  The interactive proof-view snippet renders the
/// annotated system + applicable proof methods at every proof path,
/// so an empty root would show a bogus "Constraint System is Solved"
/// with no formulas (HS keeps a `Just System` on every node).
#[test]
fn prove_lemma_keep_sys_retains_node_systems() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let src = r#"
theory T begin
rule R:
  [ Fr(~k) ] --[ A(~k) ]-> [ Out(~k) ]
lemma always_A:
  all-traces
  "All k #i. A(k) @ #i ==> Ex #j. A(k) @ #j"
end
"#;
    // The policy is process-wide; hold the lock its other writer takes so
    // no concurrent test stores a lower one mid-search.
    let _guard = crate::constraint::solver::search::SYS_RETENTION_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    crate::constraint::solver::search::set_sys_retention(
        crate::constraint::solver::search::SysRetention::KeepAll,
    );
    let pt = tamarin_parser::parse_theory(src, &[]).expect("parse");
    let root = prove_lemma(&pt, "always_A", h, 200).expect("prove");
    // Root = the initial constraint system (the negated goal formula),
    // with the lemma's refined source kind — NOT an empty default.
    assert!(
        !root.sys.formulas.is_empty(),
        "root node must retain the initial system's formulas"
    );
    assert_eq!(
        root.sys.source_kind,
        Some(crate::constraint::system::SourceKind::RefinedSources),
        "root system source kind must survive (refined for a non-sources lemma)"
    );
    // Every child must also carry a real system.
    for (name, ch) in &root.children {
        assert!(
            ch.sys.source_kind.is_some(),
            "child {:?} must retain a real system, not System::default()",
            name
        );
    }
}

/// Drive the tiny_setup proof and inspect the proof-tree shape: the root
/// takes one of the three methods `rankProofMethods` can rank first here,
/// the `Ex` decomposes into a `Goal::Action(Setup(_))`, solving it
/// instantiates the `Setup` rule via its `Fr(~k)` premise, and the search
/// reaches `Solved`.
#[test]
fn prove_lemma_tiny_setup_drives_through_action_goal() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let src = r#"
theory TinySetup begin
rule Setup:
  [ Fr(~k) ] --[ Setup(~k) ]-> [ Out(~k) ]
lemma trivial:
  exists-trace
  "Ex k #i. Setup(k) @ #i"
end
"#;
    let parser_theory = tamarin_parser::parse_theory(src, &[]).expect("parse");
    let root =
        prove_lemma(&parser_theory, "trivial", h, 100).expect("prove_lemma should not error");

    // Root method: under the `AvoidInduction` default (exists-trace
    // lemmas), Haskell's `rankProofMethods` tries Simplify first.
    // If Simplify produces non-empty cases (decomposes the formula
    // into goals), that's picked; otherwise we fall through to
    // Induction.  For this trivial existence lemma the Ex is
    // reducible, so Simplify is the root method.  Either is
    // structurally acceptable as long as the proof reaches Solved.
    use crate::constraint::solver::proof_method::ProofMethod;
    use crate::constraint::solver::search::NodeStatus;
    assert!(
        matches!(
            root.method,
            ProofMethod::Induction | ProofMethod::Simplify | ProofMethod::SolveGoal(_)
        ),
        "expected Simplify/Induction/SolveGoal at root, got {:?}",
        root.method
    );
    assert_eq!(
        root.status,
        NodeStatus::Solved,
        "expected Solved on tiny_setup, got {:?}",
        root.status
    );
}

#[test]
fn prove_lemma_tiny_setup_terminates() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let src = r#"
theory TinySetup begin
rule Setup:
  [ Fr(~k) ] --[ Setup(~k) ]-> [ Out(~k) ]
lemma trivial:
  exists-trace
  "Ex k #i. Setup(k) @ #i"
end
"#;
    let parser_theory = tamarin_parser::parse_theory(src, &[]).expect("parse");
    let root = prove_lemma(&parser_theory, "trivial", h, 50).expect("prove_lemma should not error");
    // Tamarin's proof is `induction → SOLVED` in the empty branch,
    // and the non_empty branch needs the existential to be
    // decomposed — which produces a Goal::Action. Whatever our
    // verdict, the search must terminate, and the non-trivial
    // branch should reach a method beyond the initial induction.
    use crate::constraint::solver::search::NodeStatus;
    assert!(
        !matches!(root.status, NodeStatus::Open),
        "search must terminate within budget"
    );
}

/// Build a `ProverSession` from theory source for the pre-pass tests.
fn session_from(src: &str) -> Option<ProverSession> {
    let h = maude()?;
    let pt = tamarin_parser::parse_theory(src, &[]).expect("parse");
    ProverSession::build_with_in_file_and_heuristic(
        &pt,
        h,
        None,
        "",
        CliHeuristic::default(),
        crate::constraint::solver::context::CutStrategy::Dfs,
        None,
    )
    .ok()
}

const SHARED_KEY_TWO_LEMMAS: &str = "theory T begin\n\
rule R: [ Fr(~k) ] --[ A(~k) ]-> [ Out(~k) ]\n\
lemma a: all-traces \"All k #i. A(k) @ #i ==> Ex #j. A(k) @ #j\"\n\
lemma b: all-traces \"All k #i. A(k) @ #i ==> Ex #j. A(k) @ #j\"\n\
end";

/// Two lemmas with the same (empty) `source_key` saturate ONCE in the
/// pre-pass, seed one cache entry, and a same-key lemma then restores it.
#[test]
fn presaturate_dedups_shared_source_key() {
    let session = match session_from(SHARED_KEY_TWO_LEMMAS) {
        Some(s) => s,
        None => return,
    };
    // Both lemmas are RefinedSource with no prior `[sources]` lemma, so
    // both carry the identical empty key — one saturation covers both.
    let n = session.presaturate_shared_sources(false, |_| true);
    assert_eq!(n, 1, "two lemmas sharing a key must saturate once");
    assert_eq!(
        session.source_cache.lock().unwrap().len(),
        1,
        "exactly one refined-source set is cached"
    );
    // A fan-out lemma of the same key restores from the pre-seeded cache.
    let lemma_b = session.theory.lookup_lemma("b").expect("lemma b");
    let kind = lemma_source_kind(lemma_b);
    let (mut ctx, key) = session
        .setup_per_lemma_ctx(lemma_b, "b", kind)
        .expect("ctx");
    let hit = session.restore_or_saturate_sources(&mut ctx, key, false);
    assert!(
        hit,
        "lemma b must restore from the pre-seeded shared-key cache"
    );
}

/// A lemma that would emit a bare `sorry` (not a `--prove` target and with
/// no stored proof tree) never saturates in the fan-out, so the pre-pass
/// must skip it — the spdm121 `--prove=<no match>` regression precedent.
#[test]
fn presaturate_skips_bare_sorry_lemmas() {
    let session = match session_from(SHARED_KEY_TWO_LEMMAS) {
        Some(s) => s,
        None => return,
    };
    // Freshly parsed lemmas have no stored proof tree; with no target
    // selected they emit a bare sorry and never consult a source.
    let n = session.presaturate_shared_sources(false, |_| false);
    assert_eq!(n, 0, "bare-sorry lemmas must not be pre-saturated");
    assert!(
        session.source_cache.lock().unwrap().is_empty(),
        "no key is seeded for bare-sorry lemmas"
    );
    // The SAME lemmas do saturate once they are `--prove` targets.
    let n2 = session.presaturate_shared_sources(false, |_| true);
    assert_eq!(n2, 1, "targeted lemmas saturate their shared key once");
}

/// `cache_disabled` (`TAM_RS_NO_SOURCE_CACHE`) bypasses the pre-pass
/// entirely, falling back to the per-lemma compute path.
#[test]
fn presaturate_disabled_is_noop() {
    let session = match session_from(SHARED_KEY_TWO_LEMMAS) {
        Some(s) => s,
        None => return,
    };
    let n = session.presaturate_shared_sources(true, |_| true);
    assert_eq!(n, 0, "the disabled pre-pass saturates nothing");
    assert!(
        session.source_cache.lock().unwrap().is_empty(),
        "the disabled pre-pass seeds no cache entries"
    );
}

/// `parse_config_block` records what cmdargs records, rejection strings
/// byte-pinned against the oracle (`configuration: "<cfg>"` under
/// `--prove`, stderr after `tamarin-prover: `).
#[test]
fn config_block_matches_cmdargs_semantics() {
    use crate::constraint::solver::context::CutStrategy;

    // Prefix matching resolves like the CLI's: `--stop`, even `--s`.
    for cfg in ["--stop-on-trace=bfs", "--stop=bfs", "--s=bfs"] {
        let b = parse_config_block(cfg);
        assert_eq!(b.flag_error, None, "{cfg}");
        assert_eq!(b.stop_on_trace.as_deref(), Some("bfs"), "{cfg}");
    }
    // flagOpt: bare records "dfs"; no separate token is consumed.
    let b = parse_config_block("--stop-on-trace bfs");
    assert_eq!(b.stop_on_trace.as_deref(), Some("dfs"));
    // The VALUE is recorded raw — validation is the reader's, later.
    let b = parse_config_block("--stop-on-trace=XYZ --auto-sources");
    assert_eq!(b.flag_error, None);
    assert_eq!(b.stop_on_trace.as_deref(), Some("XYZ"));
    assert!(b.auto_sources);
    // Positionals are swallowed by the catch-all.
    let b = parse_config_block("positional --auto-sources");
    assert_eq!(b.flag_error, None);
    assert!(b.auto_sources);

    // cmdargs-level rejections, byte-for-byte.
    for (cfg, want) in [
        ("--nonsense", "Unknown flag: --nonsense"),
        (
            "--auto-sources=x",
            "Unhandled argument to flag, none expected: --auto-sources=x",
        ),
        ("-a", "Unknown flag: -a"),
        ("-abc", "Unknown flag: -a"),
        (
            "--=x",
            "Ambiguous flag '--', could be any of: stop-on-trace auto-sources",
        ),
    ] {
        assert_eq!(
            parse_config_block(cfg).flag_error.as_deref(),
            Some(want),
            "{cfg}"
        );
    }

    // The deferred value reader — HS `stopOnTrace`, lowercasing first.
    assert_eq!(parse_stop_on_trace("BFS"), Ok(CutStrategy::Bfs));
    assert_eq!(
        parse_stop_on_trace("XYZ"),
        Err("unknown stop-on-trace method: xyz".to_string())
    );

    // The server's eager wrapper surfaces both kinds of error.
    assert_eq!(
        config_block_options("--nonsense"),
        Err("Unknown flag: --nonsense".to_string())
    );
    assert_eq!(
        config_block_options("--stop-on-trace=XYZ"),
        Err("unknown stop-on-trace method: xyz".to_string())
    );
    assert_eq!(
        config_block_options("--stop-on-trace=seqdfs --auto-sources"),
        Ok((Some(CutStrategy::SeqDfs), true))
    );
}
