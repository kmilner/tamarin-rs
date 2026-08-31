// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::fact::LNFact;
use tamarin_term::lterm::{LSort, LVar};

// ===== HS `M.Map` / `Data.Set` order helpers =====

fn node_id(name: &str, idx: u64) -> NodeId {
    LVar::new(name, LSort::Node, idx)
}

/// A bare rule instance — the order helpers only ever read the node id.
fn bare_rule() -> RuleACInst {
    crate::rule::Rule::new(
        crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::Coerce),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    )
}

#[test]
fn nodes_in_map_order_is_ascending_node_id_not_insertion_order() {
    let mut s = System::empty();
    // `Ord LVar` compares idx FIRST, then sort, then name, so the
    // ascending-idx order here is the reverse of the alphabetical one.
    for id in [node_id("a", 2), node_id("b", 1), node_id("c", 0)] {
        s.nodes_mut().push((id, bare_rule()));
    }
    let ordered: Vec<(u64, String)> = s
        .nodes_in_map_order()
        .iter()
        .map(|p| (p.0.idx, p.0.name.to_string()))
        .collect();
    assert_eq!(
        ordered,
        vec![
            (0, "c".to_string()),
            (1, "b".to_string()),
            (2, "a".to_string())
        ]
    );
    // The stored `Vec` keeps INSERTION order — `set_nodes` picks the
    // surviving rule at an id collision by it — so only the view reorders.
    let stored: Vec<u64> = s.nodes.iter().map(|(id, _)| id.idx).collect();
    assert_eq!(stored, vec![2, 1, 0]);
    // The slice-taking free function is the same materialisation.
    let via_slice: Vec<u64> = nodes_in_map_order(&s.nodes)
        .iter()
        .map(|p| p.0.idx)
        .collect();
    assert_eq!(via_slice, vec![0, 1, 2]);
}

#[test]
fn edges_and_less_atoms_come_out_in_set_order() {
    use crate::constraint::constraints::Reason;
    use crate::rule::{ConcIdx, PremIdx};
    let mut s = System::empty();
    let n = |i| node_id("i", i);
    // `Ord Edge` is derived — `src` then `tgt` — so the (1, ConcIdx 0)
    // edge precedes the (1, ConcIdx 1) one regardless of its target.
    s.content_mut().edges = vec![
        Edge {
            src: (n(2), ConcIdx(0)),
            tgt: (n(3), PremIdx(0)),
        },
        Edge {
            src: (n(1), ConcIdx(1)),
            tgt: (n(2), PremIdx(0)),
        },
        Edge {
            src: (n(1), ConcIdx(0)),
            tgt: (n(9), PremIdx(0)),
        },
    ];
    let edge_order: Vec<(u64, usize)> = s
        .edges_in_set_order()
        .iter()
        .map(|e| (e.src.0.idx, e.src.1 .0))
        .collect();
    assert_eq!(edge_order, vec![(1, 0), (1, 1), (2, 0)]);
    // `Ord LessAtom` is `(smaller, larger)` and IGNORES the reason tag:
    // ordering by `Reason` would put Adversary last, not first.
    s.content_mut().less_atoms = vec![
        LessAtom::new(n(2), n(3), Reason::Formula),
        LessAtom::new(n(1), n(5), Reason::NormalForm),
        LessAtom::new(n(1), n(2), Reason::Adversary),
    ];
    let less_order: Vec<(u64, u64)> = s
        .less_atoms_in_set_order()
        .iter()
        .map(|la| (la.smaller.idx, la.larger.idx))
        .collect();
    assert_eq!(less_order, vec![(1, 2), (1, 5), (2, 3)]);
}

// ===== verified-identity subst_system skip: stamp lifecycle =====

#[test]
fn next_stamp_strictly_increases() {
    let a = tamarin_utils::next_stamp();
    let b = tamarin_utils::next_stamp();
    let c = tamarin_utils::next_stamp();
    assert!(a < b && b < c);
    assert_ne!(a, 0, "0 is the reserved sentinel");
}

#[test]
fn empty_mints_fresh_stamps_and_no_marker() {
    let s = System::empty();
    assert_ne!(s.content_stamp.get(), 0);
    assert_ne!(s.subst_stamp.get(), 0);
    assert_eq!(s.subst_applied_marker.get(), None);
}

#[test]
fn clone_copies_stamps_and_marker_verbatim() {
    let s = System::empty();
    s.subst_applied_marker.set(Some((7, 9)));
    let c = s.clone();
    assert_eq!(c.content_stamp.get(), s.content_stamp.get());
    assert_eq!(c.subst_stamp.get(), s.subst_stamp.get());
    assert_eq!(c.subst_applied_marker.get(), Some((7, 9)));
}

#[test]
fn content_mutation_bumps_content_stamp_leaving_parent_untouched() {
    let parent = System::empty();
    let c0 = parent.content_stamp.get();
    let mut child = parent.clone();
    assert_eq!(child.content_stamp.get(), c0, "clone inherits verbatim");
    let v = LVar::new("k", LSort::Msg, 0);
    let f = LNFact::new(crate::fact::FactTag::Out, vec![]);
    child.add_goal(Goal::Action(v, f));
    assert_ne!(child.content_stamp.get(), c0, "add_goal bumps the child");
    assert_eq!(parent.content_stamp.get(), c0, "parent untouched");
}

#[test]
fn set_eq_store_bumps_subst_stamp() {
    let mut s = System::empty();
    let b0 = s.subst_stamp.get();
    s.set_eq_store(std::sync::Arc::new(
        crate::tools::equation_store::EquationStore::default(),
    ));
    assert_ne!(s.subst_stamp.get(), b0);
}

#[test]
fn eq_store_mut_bumps_subst_stamp() {
    let mut s = System::empty();
    let b0 = s.subst_stamp.get();
    let _ = s.eq_store_mut();
    assert_ne!(s.subst_stamp.get(), b0);
}

#[test]
fn stamps_and_marker_excluded_from_partial_eq() {
    let a = System::empty();
    let b = a.clone();
    // Diverge every stamp/marker cell but keep content identical.
    b.content_stamp.set(a.content_stamp.get().wrapping_add(1));
    b.subst_stamp.set(a.subst_stamp.get().wrapping_add(1));
    b.subst_applied_marker.set(Some((123, 456)));
    b.formulas_stamp.set(a.formulas_stamp.get().wrapping_add(1));
    b.solved_formulas_stamp
        .set(a.solved_formulas_stamp.get().wrapping_add(1));
    assert_eq!(a, b, "PartialEq must ignore the stamp/marker cells");
}

/// The untracked write doors (`content_mut_untracked` and the per-store
/// `formulas_mut_untracked` / `solved_formulas_mut_untracked`; no
/// `content_stamp` bump, no max-cache invalidation) may be called ONLY from
/// the closed set of whole-system rewriters that manage the
/// stamps/caches themselves.  A new caller fails the build until its stamp
/// reasoning is established (the subst axis is sealed separately:
/// `SealedEqStore` makes a raw `eq_store` assignment inexpressible).
///
/// Scans the WHOLE crate `src/` (the methods are `pub(crate)`, so their
/// visibility scope is the whole crate — the scan scope must match).  For
/// each door CALL it records the nearest preceding `fn <name>` and asserts
/// the caller-name set is within the whitelist.  Separately it FORBIDS any
/// raw `content_mut_untracked().formulas` / `.solved_formulas` write, which
/// would bypass the per-store formula stamp bump — those must route through
/// the bumping accessors.  And it flags any content-door call whose
/// `&mut SystemContent` ESCAPES (not immediately projected to a `.field`),
/// since formula writes through an escaped binding are invisible to the
/// single-line forbid scan.
#[test]
fn content_untracked_callers_are_enumerated() {
    const ALLOWED: &[&str] = &[
        "subst_system_once",
        "set_nodes",
        "rename_precise_system",
        "normalise_less_atoms_pass",
    ];
    // Fns where the content door's `&mut SystemContent` may escape into a
    // binding (each audited to write no formula store through it):
    // `normalise_less_atoms_pass` binds it to borrow-split `eq_store.subst`
    // reads from `less_atoms` writes.
    const ESCAPE_ALLOWED: &[&str] = &["normalise_less_atoms_pass"];
    let src_root = concat!(env!("CARGO_MANIFEST_DIR"), "/src");
    // Build the call needles by concatenation so THIS test's own source
    // (and the accessors' doc comments) never contain a literal verbatim and
    // cannot self-flag.  A CALL is `.<method>()`; the definition
    // `fn <method>` has no leading dot and is excluded.  The per-store
    // untracked formula accessors carry the SAME discipline as
    // `content_mut_untracked` — they bump only the per-store stamp, so their
    // caller must own the `content_stamp` bookkeeping — hence the same
    // whitelist.  (`.solved_formulas_mut_untracked()` does not contain
    // `.formulas_mut_untracked()` as a substring — `formulas` is preceded by
    // `_`, not `.` — so the two needles are independent.)
    let call_needles = [
        [".", "content_mut_untracked", "()"].concat(),
        [".", "formulas_mut_untracked", "()"].concat(),
        [".", "solved_formulas_mut_untracked", "()"].concat(),
    ];
    // Raw `content_mut_untracked().formulas` / `.solved_formulas` writes
    // bypass the per-store stamp bump, so they are FORBIDDEN everywhere:
    // every untracked formula write must route through the bumping accessor.
    // (`.lemmas` is intentionally NOT forbidden — it has no per-store stamp.)
    let forbid_needles = [
        ["content_mut_untracked", "().", "formulas"].concat(),
        ["content_mut_untracked", "().", "solved_formulas"].concat(),
    ];
    let mut offenders: Vec<String> = Vec::new();
    let mut forbidden: Vec<String> = Vec::new();
    let mut escapes: Vec<String> = Vec::new();
    // These counters record how many times each door needle and the escape
    // shape matched.  A scan that matches nothing asserts nothing.  So the
    // code below checks that these counts are not zero.
    let mut seen = [0usize; 3];
    let mut escaping = 0usize;
    let mut files: Vec<std::path::PathBuf> = Vec::new();
    let mut stack = vec![std::path::PathBuf::from(src_root)];
    while let Some(dir) = stack.pop() {
        for entry in std::fs::read_dir(&dir).expect("read src dir") {
            let path = entry.expect("dir entry").path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
                files.push(path);
            }
        }
    }
    // Out-of-line test modules — `#[cfg(test)]` + `#[path = "<file>"]` +
    // `mod <name>;` in a parent `foo.rs` puts the module's code in a sibling
    // `<file>` (without the path attribute it would be `foo/<name>.rs`) — are
    // whole files of test code; collect them so the scan below skips them
    // entirely.
    let mut test_files: tamarin_utils::FastSet<std::path::PathBuf> =
        tamarin_utils::FastSet::default();
    for path in &files {
        let src = std::fs::read_to_string(path).expect("read source");
        let mut lines = src.lines().peekable();
        while let Some(line) = lines.next() {
            if line.trim_start() != "#[cfg(test)]" {
                continue;
            }
            let path_attr = lines
                .peek()
                .and_then(|n| n.trim_start().strip_prefix("#[path = \""))
                .and_then(|r| r.strip_suffix("\"]"))
                .map(str::to_string);
            if path_attr.is_some() {
                lines.next();
            }
            if let Some(name) = lines
                .peek()
                .and_then(|n| n.trim_start().strip_prefix("mod "))
                .and_then(|r| r.strip_suffix(';'))
            {
                test_files.insert(match &path_attr {
                    Some(file) => path.parent().expect("src file has a parent").join(file),
                    None => path.with_extension("").join(format!("{name}.rs")),
                });
            }
        }
    }
    for path in &files {
        if test_files.contains(path) {
            continue;
        }
        let src = std::fs::read_to_string(path).expect("read source");
        let mut cur_fn = String::from("<file-scope>");
        for line in src.lines() {
            let trimmed = line.trim_start();
            // Stop at the file's `#[cfg(test)]` / `mod tests` boundary:
            // unit tests legitimately exercise the accessor and must not
            // count as production callers (inline test modules sit at
            // file end).
            if trimmed.starts_with("#[cfg(test)]") || trimmed.starts_with("mod tests") {
                break;
            }
            if let Some(rest) = trimmed
                .strip_prefix("fn ")
                .or_else(|| trimmed.strip_prefix("pub fn "))
                .or_else(|| trimmed.strip_prefix("pub(crate) fn "))
            {
                let name: String = rest
                    .chars()
                    .take_while(|c| c.is_alphanumeric() || *c == '_')
                    .collect();
                if !name.is_empty() {
                    cur_fn = name;
                }
            }
            if trimmed.starts_with("//") {
                continue;
            }
            for (i, needle) in call_needles.iter().enumerate() {
                if line.contains(needle) {
                    seen[i] += 1;
                    if !ALLOWED.contains(&cur_fn.as_str()) {
                        offenders.push(format!("{} in fn {}", path.display(), cur_fn));
                    }
                }
            }
            if forbid_needles.iter().any(|n| line.contains(n)) {
                forbidden.push(format!("{} in fn {}", path.display(), cur_fn));
            }
            // Escape check (content door only — the formula doors bump
            // before handing out their `&mut Vec`, so escaping those is
            // harmless): a call NOT followed by `.` hands the raw
            // `&mut SystemContent` to a binding/argument, where a later
            // formula write would evade the forbid needles above.
            for (pos, _) in line.match_indices(&call_needles[0]) {
                let next = line[pos + call_needles[0].len()..].chars().next();
                if next != Some('.') {
                    escaping += 1;
                    if !ESCAPE_ALLOWED.contains(&cur_fn.as_str()) {
                        escapes.push(format!("{} in fn {}", path.display(), cur_fn));
                    }
                }
            }
        }
    }
    assert!(
        offenders.is_empty(),
        "an untracked content/formula door was called from non-whitelisted \
             fn(s) (verify its stamp discipline, then add to ALLOWED): {offenders:?}"
    );
    assert!(
        forbidden.is_empty(),
        "raw untracked formula-store write(s) bypass the per-store stamp \
             bump — route them through formulas_mut_untracked / \
             solved_formulas_mut_untracked: {forbidden:?}"
    );
    assert!(
        escapes.is_empty(),
        "the untracked content door's &mut SystemContent escapes without a \
             field projection — audit that no formula store is written through \
             it, then add the fn to ESCAPE_ALLOWED: {escapes:?}"
    );
    // A scan that matches nothing also satisfies the three assertions above.
    // A renamed accessor gives that result.  So does a `src` walk that
    // reaches no file in the crate.  The checks below therefore assert that
    // every needle still matches something.  A rename must then update the
    // needles, and it cannot silence this discipline.
    assert!(
        seen.iter().all(|hits| *hits > 0),
        "a door needle matched no call at all — the accessor was renamed or \
             the scan reached no production file, which silences this test: \
             {call_needles:?} hits {seen:?}"
    );
    assert!(
        escaping > 0,
        "no content-door call hands out an unprojected &mut SystemContent any \
             more, so the escape scan proves nothing — drop ESCAPE_ALLOWED and \
             this check together with the last escaping caller"
    );
}

#[test]
fn content_mut_bumps_both_stamps_and_invalidates_caches() {
    let mut s = System::empty();
    s.max_var_idx_cache.set(Some(5));
    s.node_max_cache.set(Some(5));
    let c0 = s.content_stamp.get();
    let b0 = s.subst_stamp.get();
    let _ = s.content_mut();
    assert_ne!(s.content_stamp.get(), c0, "content_mut bumps content_stamp");
    assert_ne!(s.subst_stamp.get(), b0, "content_mut bumps subst_stamp");
    assert_eq!(
        s.max_var_idx_cache.get(),
        None,
        "content_mut clears max cache"
    );
    assert_eq!(
        s.node_max_cache.get(),
        None,
        "content_mut clears node cache"
    );
}

#[test]
fn content_mut_untracked_bumps_nothing() {
    let mut s = System::empty();
    s.max_var_idx_cache.set(Some(5));
    let c0 = s.content_stamp.get();
    let b0 = s.subst_stamp.get();
    let _ = s.content_mut_untracked();
    assert_eq!(
        s.content_stamp.get(),
        c0,
        "untracked door does not bump content"
    );
    assert_eq!(
        s.subst_stamp.get(),
        b0,
        "untracked door does not bump subst"
    );
    assert_eq!(
        s.max_var_idx_cache.get(),
        Some(5),
        "untracked door leaves caches"
    );
}

#[test]
fn deref_reads_reach_content_fields() {
    // Compile-level coverage that reads auto-deref through `SystemContent`.
    let s = System::empty();
    assert_eq!(s.nodes.len(), 0);
    assert_eq!(s.edges.len(), 0);
    assert_eq!(s.less_atoms.len(), 0);
    assert_eq!(s.formulas.len(), 0);
    assert_eq!(s.goals.len(), 0);
    assert!(s.last_atom.is_none());
    assert!(s.eq_store.subst.is_empty());
}

#[test]
fn formula_accessors_bump_content_stamp() {
    let mut s = System::empty();
    for pick in 0..3 {
        let c0 = s.content_stamp.get();
        match pick {
            0 => {
                let _ = s.formulas_mut();
            }
            1 => {
                let _ = s.solved_formulas_mut();
            }
            _ => {
                let _ = s.lemmas_mut();
            }
        }
        assert_ne!(
            s.content_stamp.get(),
            c0,
            "formula accessor bumps content_stamp"
        );
    }
}

#[test]
fn tracked_formula_accessors_bump_per_store_stamp() {
    let mut s = System::empty();
    let f0 = s.formulas_stamp.get();
    let _ = s.formulas_mut();
    assert_ne!(
        s.formulas_stamp.get(),
        f0,
        "formulas_mut bumps formulas_stamp"
    );
    let sv0 = s.solved_formulas_stamp.get();
    let _ = s.solved_formulas_mut();
    assert_ne!(
        s.solved_formulas_stamp.get(),
        sv0,
        "solved_formulas_mut bumps its stamp"
    );
}

#[test]
fn untracked_formula_accessors_bump_only_per_store_stamp() {
    let mut s = System::empty();
    let c0 = s.content_stamp.get();
    let b0 = s.subst_stamp.get();
    s.max_var_idx_cache.set(Some(5));
    let f0 = s.formulas_stamp.get();
    let _ = s.formulas_mut_untracked();
    assert_eq!(
        s.content_stamp.get(),
        c0,
        "untracked formula door leaves content_stamp"
    );
    assert_eq!(
        s.subst_stamp.get(),
        b0,
        "untracked formula door leaves subst_stamp"
    );
    assert_eq!(
        s.max_var_idx_cache.get(),
        Some(5),
        "untracked formula door leaves caches"
    );
    assert_ne!(
        s.formulas_stamp.get(),
        f0,
        "untracked formula door bumps formulas_stamp"
    );

    let sv0 = s.solved_formulas_stamp.get();
    let _ = s.solved_formulas_mut_untracked();
    assert_eq!(
        s.content_stamp.get(),
        c0,
        "untracked solved door leaves content_stamp"
    );
    assert_ne!(
        s.solved_formulas_stamp.get(),
        sv0,
        "untracked solved door bumps its stamp"
    );
}

#[test]
fn content_mut_bumps_per_store_formula_stamps() {
    let mut s = System::empty();
    let f0 = s.formulas_stamp.get();
    let sv0 = s.solved_formulas_stamp.get();
    let _ = s.content_mut();
    assert_ne!(
        s.formulas_stamp.get(),
        f0,
        "content_mut bumps formulas_stamp"
    );
    assert_ne!(
        s.solved_formulas_stamp.get(),
        sv0,
        "content_mut bumps solved_formulas_stamp"
    );
}

#[test]
fn mint_fresh_stamps_refreshes_per_store_and_clears_caches() {
    let s = System::empty();
    let ident = |src: &Arc<Guarded>| (Arc::clone(src), tamarin_utils::fx_hash_one(src.as_ref()));
    let _ = s.formulas_canon_table(ident);
    let _ = s.solved_formulas_canon_table(ident);
    assert!(s.formulas_canon_cache.borrow().is_some());
    assert!(s.solved_formulas_canon_cache.borrow().is_some());
    let f0 = s.formulas_stamp.get();
    let sv0 = s.solved_formulas_stamp.get();
    s.mint_fresh_stamps();
    assert_ne!(
        s.formulas_stamp.get(),
        f0,
        "mint_fresh_stamps refreshes formulas_stamp"
    );
    assert_ne!(
        s.solved_formulas_stamp.get(),
        sv0,
        "mint_fresh_stamps refreshes solved stamp"
    );
    assert!(
        s.formulas_canon_cache.borrow().is_none(),
        "mint_fresh_stamps drops formulas cache"
    );
    assert!(
        s.solved_formulas_canon_cache.borrow().is_none(),
        "mint_fresh_stamps drops solved cache"
    );
}

#[test]
fn canon_table_stamp_hit_reuses_and_miss_rebuilds_incrementally() {
    let mut s = System::empty();
    s.formulas_mut().push(Arc::new(crate::guarded::gfalse()));
    s.formulas_mut().push(Arc::new(crate::guarded::gtrue()));

    let calls = Cell::new(0u32);
    let canon = |src: &Arc<Guarded>| {
        calls.set(calls.get() + 1);
        (Arc::clone(src), tamarin_utils::fx_hash_one(src.as_ref()))
    };

    // First force: full build canons every entry.
    let t1 = s.formulas_canon_table(canon);
    assert_eq!(t1.entries.len(), 2);
    assert_eq!(calls.get(), 2, "full build canons every entry");

    // Unchanged stamp: verbatim reuse of the same table Arc, zero canon.
    let t2 = s.formulas_canon_table(canon);
    assert!(Arc::ptr_eq(&t1, &t2), "stamp hit reuses the same table Arc");
    assert_eq!(calls.get(), 2, "stamp hit runs no canon");

    // Push a third formula (bumps formulas_stamp); the first two keep their
    // `Arc` identity, so only the new entry is recanoned.
    s.formulas_mut().push(Arc::new(crate::guarded::gfalse()));
    let t3 = s.formulas_canon_table(canon);
    assert!(!Arc::ptr_eq(&t1, &t3), "stamp miss builds a new table");
    assert_eq!(t3.entries.len(), 3);
    assert_eq!(
        calls.get(),
        3,
        "incremental rebuild recanons only the changed entry"
    );
    assert!(
        Arc::ptr_eq(&t1.entries[0].0, &t3.entries[0].0),
        "unchanged src Arc reused"
    );
    assert!(
        Arc::ptr_eq(&t1.entries[1].0, &t3.entries[1].0),
        "unchanged src Arc reused"
    );
}

#[test]
fn canon_cache_shared_then_independent_across_clone() {
    let mut a = System::empty();
    a.formulas_mut().push(Arc::new(crate::guarded::gfalse()));
    let ident = |src: &Arc<Guarded>| (Arc::clone(src), tamarin_utils::fx_hash_one(src.as_ref()));
    let ta = a.formulas_canon_table(ident);

    // A clone inherits the stamp AND shares the cached generation.
    let mut b = a.clone();
    let tb = b.formulas_canon_table(ident);
    assert!(
        Arc::ptr_eq(&ta, &tb),
        "a clone shares the parent's cached table (equal stamp)"
    );

    // Mutating `b` bumps only `b`'s stamp: `b` rebuilds, `a` is undisturbed.
    b.formulas_mut().push(Arc::new(crate::guarded::gtrue()));
    let tb2 = b.formulas_canon_table(ident);
    assert!(!Arc::ptr_eq(&tb, &tb2), "b rebuilds after its own mutation");
    let ta2 = a.formulas_canon_table(ident);
    assert!(
        Arc::ptr_eq(&ta, &ta2),
        "a still reuses its generation (untouched)"
    );
}

#[test]
fn set_last_atom_bumps_content_stamp() {
    let mut s = System::empty();
    let c0 = s.content_stamp.get();
    s.set_last_atom(None);
    assert_ne!(s.content_stamp.get(), c0);
}

#[test]
fn cleanup_invalidates_max_var_idx_cache() {
    use crate::constraint::solver::reduction::{bounds_max, bounds_max_uncached};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    // Per-name idxs dense from 0 make `rename_precise_system` the
    // identity (no remap ⇒ no invalidation from the rename itself),
    // while the subst holds the global max idx: `x.1` occurs nowhere
    // outside the subst range, so `cleanup`'s subst-clear lowers the
    // true max from 1 to 0.
    let mut s = System::empty();
    s.set_last_atom(Some(LVar::new("i", LSort::Node, 0)));
    s.eq_store_mut().subst = tamarin_term::subst::Subst::from_list([(
        LVar::new("x", LSort::Msg, 0),
        Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 1))),
    )]);
    // Populate the cache with the pre-cleanup max (held by the subst).
    assert_eq!(bounds_max(&s), 1);
    let s = s.cleanup();
    assert_eq!(bounds_max_uncached(&s), 0);
    // The cached read must match — a stale cache would return 1 here.
    assert_eq!(bounds_max(&s), 0);
}

#[test]
fn take_eq_store_bumps_subst_stamp_and_takes() {
    let mut s = System::empty();
    let b0 = s.subst_stamp.get();
    let taken = s.take_eq_store();
    assert_ne!(s.subst_stamp.get(), b0, "take_eq_store bumps subst_stamp");
    assert!(taken.subst.is_empty());
}

#[test]
fn add_goal_idempotent() {
    let mut s = System::empty();
    let v = LVar::new("k", LSort::Msg, 0);
    let f = LNFact::new(crate::fact::FactTag::Out, vec![]);
    let g = Goal::Action(v, f);
    s.add_goal(g.clone());
    s.add_goal(g);
    assert_eq!(s.goals.len(), 1);
}

/// `add_goal_with_loop_flag` dedups on `==` over the whole `Goal`.  Two
/// independently built, structurally equal `Disj` goals therefore land in one
/// slot: the second insertion ORs its `looping` flag into the stored status,
/// keeps the smaller `nr`, and leaves the stored goal in place, while
/// `next_goal_nr` still advances once per call (HS `insertGoalStatus` and the
/// `combineGoalStatus` it merges with, Reduction.hs:513-523).
#[test]
fn add_goal_merges_structurally_equal_disj_goals() {
    use crate::constraint::constraints::Disj;
    use crate::guarded::{gtrue, Guarded};

    let mut s = System::empty();
    let disj = || Goal::Disj(Disj::<Guarded>::new(vec![gtrue()]));
    s.add_goal_with_loop_flag(disj(), false);
    s.add_goal_with_loop_flag(disj(), true);
    assert_eq!(s.goals.len(), 1);
    assert_eq!(s.goals[0].0, disj());
    assert!(s.goals[0].1.looping);
    assert_eq!(s.goals[0].1.nr, 0);
    assert_eq!(s.next_goal_nr, 2);

    // A different Disj is a different key.
    s.add_goal_with_loop_flag(Goal::Disj(Disj::<Guarded>::new(Vec::new())), false);
    assert_eq!(s.goals.len(), 2);
}

#[test]
fn insert_lemma_flattens_top_level_conj() {
    let mut s = System::empty();
    // Use Atom-bearing lemmas so the smart Conj flattening doesn't
    // optimise them away. We just need two leaves that don't
    // recurse further into Conj.
    use crate::atom::ProtoAtom;
    use crate::formula::BLNTerm;
    use tamarin_term::lterm::{BVar, LSort, LVar};
    use tamarin_term::vterm::var_term;
    let mkvar = |n: &str| -> BLNTerm { var_term(BVar::Free(LVar::new(n, LSort::Node, 0))) };
    let l1 = crate::guarded::Guarded::Atom(ProtoAtom::Last(mkvar("i")));
    let l2 = crate::guarded::Guarded::Atom(ProtoAtom::Last(mkvar("j")));
    s.insert_lemma(crate::guarded::Guarded::Conj(
        vec![l1.clone(), l2.clone()].into(),
    ));
    assert_eq!(s.lemmas.len(), 2);
    assert!(crate::guarded::stores_contains(&s.lemmas, &l1));
    assert!(crate::guarded::stores_contains(&s.lemmas, &l2));
}

#[test]
fn formula_to_system_exists_trace_keeps_formula() {
    use crate::theory::TraceQuantifier;
    let f = crate::guarded::gtrue();
    let sys = formula_to_system(
        Vec::new(),
        SourceKind::RawSources,
        TraceQuantifier::ExistsTrace,
        &f,
    );
    // ExistsTrace ⇒ formula kept as-is.
    assert_eq!(sys.formulas.len(), 1);
    assert_eq!(*sys.formulas[0], f);
}

#[test]
fn formula_to_system_all_traces_negates() {
    use crate::theory::TraceQuantifier;
    // For AllTraces lemma `T`, the negation is `gfalse`.
    let f = crate::guarded::gtrue();
    let sys = formula_to_system(
        Vec::new(),
        SourceKind::RawSources,
        TraceQuantifier::AllTraces,
        &f,
    );
    assert_eq!(sys.formulas.len(), 1);
    assert_eq!(*sys.formulas[0], crate::guarded::gfalse());
}

#[test]
fn formula_to_system_partitions_safety_restrictions() {
    use crate::atom::ProtoAtom;
    use crate::formula::BLNTerm;
    use crate::theory::TraceQuantifier;
    use tamarin_term::lterm::{BVar, LSort, LVar};
    use tamarin_term::vterm::var_term;
    let mkvar = |n: &str| -> BLNTerm { var_term(BVar::Free(LVar::new(n, LSort::Node, 0))) };
    // `Last(i)` has a free variable, so `is_safety_formula` rejects it.  It
    // is the non-safety arm of the partition.  It is also the one shape that
    // tells the two arms apart.  `formulas` holds exactly one entry in both
    // cases, the complete conjunction, so its length says nothing.
    let goal = crate::guarded::Guarded::Atom(ProtoAtom::Last(mkvar("j")));
    let unsafe_r = crate::guarded::Guarded::Atom(ProtoAtom::Last(mkvar("i")));
    // gtrue is a safety formula: it has no Ex and no free variables.  gfalse
    // (`Disj []`) is a safety formula too.
    let restrictions = vec![
        crate::guarded::gtrue(),
        crate::guarded::gfalse(),
        unsafe_r.clone(),
    ];
    let sys = formula_to_system(
        restrictions,
        SourceKind::RawSources,
        TraceQuantifier::ExistsTrace,
        &goal,
    );
    // The code conjoins the non-safety restriction onto the goal formula.
    // The goal is ExistsTrace, so the code does not negate it.
    assert_eq!(sys.formulas.len(), 1);
    assert_eq!(
        *sys.formulas[0],
        crate::guarded::Guarded::Conj(vec![goal, unsafe_r.clone()].into())
    );
    // Only the safety restrictions become known-true lemmas.  gtrue is
    // `Conj []`, and `insert_lemma` flattens it to nothing, because the empty
    // conjunction holds no items.  gfalse stays.
    assert!(crate::guarded::stores_contains(
        &sys.lemmas,
        &crate::guarded::gfalse()
    ));
    assert!(
        !crate::guarded::stores_contains(&sys.lemmas, &unsafe_r),
        "a non-safety restriction must not be asserted as a lemma"
    );
}

// =============================================================================
// HasFrees
// =============================================================================

use crate::constraint::constraints::{Disj, Reason, SplitId};
use crate::rule::{ConcIdx, PremIdx};
use crate::tools::equation_store::EqDisj;
use crate::tools::subterm_store::{SortedPairSet, SubtermConstraint};
use tamarin_term::lterm::{frees, frees_list, HasFrees, LNTerm};
use tamarin_term::subst::Subst;
use tamarin_term::subst_vfresh::SubstVFresh;
use tamarin_term::term::Term;
use tamarin_term::vterm::Lit;

/// A node variable, distinguished from every other fixture variable by its
/// index alone: `Ord LVar` compares the index first (LTerm.hs:546-548), so a
/// visit sequence reads off as a list of indices.
fn nvar(idx: u64) -> NodeId {
    LVar::new("i", LSort::Node, idx)
}

fn mvar(idx: u64) -> LVar {
    LVar::new("x", LSort::Msg, idx)
}

fn mterm(idx: u64) -> LNTerm {
    Term::Lit(Lit::Var(mvar(idx)))
}

/// A rule instance whose single premise holds `t`, so a walk that reaches the
/// rule shows `t`'s variables after the node id.
fn rule_holding(t: LNTerm) -> RuleACInst {
    crate::rule::Rule::new(
        crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::Coerce),
        vec![LNFact::new(crate::fact::FactTag::Out, vec![t])],
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
    use crate::atom::ProtoAtom;
    use tamarin_term::lterm::{BVar, LSort, LVar};
    use tamarin_term::vterm::var_term;
    Guarded::Atom(ProtoAtom::Last(var_term(BVar::Free(LVar::new(
        "i",
        LSort::Node,
        idx,
    )))))
}

/// A system carrying a distinct variable in every field of the Haskell record
/// (System.hs:383-392).  Each multi-element field is filled in the REVERSE of
/// its `Data.Set` / `Data.Map` order, so a walk that reads the stored `Vec`
/// order instead of the container order comes out backwards.
fn one_variable_per_field_system() -> System {
    let mut s = System::empty();
    s.content_mut().nodes = Arc::new(vec![
        (nvar(20), rule_holding(mterm(21))),
        (nvar(10), rule_holding(mterm(11))),
    ]);
    s.content_mut().edges = vec![
        Edge {
            src: (nvar(32), ConcIdx(0)),
            tgt: (nvar(33), PremIdx(0)),
        },
        Edge {
            src: (nvar(30), ConcIdx(0)),
            tgt: (nvar(31), PremIdx(0)),
        },
    ];
    s.content_mut().less_atoms = vec![
        LessAtom::new(nvar(42), nvar(43), Reason::Fresh),
        LessAtom::new(nvar(40), nvar(41), Reason::Fresh),
    ];
    s.content_mut().last_atom = Some(nvar(50));
    {
        let st = s.subterm_store_mut();
        // The negative subterms carry the HIGHEST indices of the store, so the
        // sequence tells `negSt <> st <> solvedSt` (SubtermStore.hs:548-549)
        // apart from any index-ordered walk.
        st.neg_subterms = SortedPairSet::rebuild_from(vec![(mterm(90), mterm(91))]);
        st.old_neg_subterms = SortedPairSet::rebuild_from(vec![(mterm(98), mterm(99))]);
        st.subterms = vec![subterm_constraint(72, 73), subterm_constraint(70, 71)];
        st.solved_subterms = vec![subterm_constraint(80, 81)];
    }
    {
        let es = s.eq_store_mut();
        es.subst = Subst::from_list(vec![(mvar(102), mterm(103)), (mvar(100), mterm(101))]);
        es.conj = vec![EqDisj {
            split_id: SplitId(0),
            substs: vec![
                SubstVFresh::from_list(vec![(mvar(112), mterm(113))]),
                SubstVFresh::from_list(vec![(mvar(110), mterm(111))]),
            ],
        }];
    }
    s.content_mut().formulas = vec![Arc::new(last_formula(121)), Arc::new(last_formula(120))];
    s.content_mut().solved_formulas = vec![Arc::new(last_formula(130))];
    s.content_mut().lemmas = vec![Arc::new(last_formula(140))];
    s.content_mut().goals = Arc::new(vec![
        (
            Goal::Chain((nvar(160), ConcIdx(0)), (nvar(161), PremIdx(0))),
            GoalStatus::default(),
        ),
        (
            Goal::Action(
                nvar(150),
                LNFact::new(crate::fact::FactTag::Out, vec![mterm(151)]),
            ),
            GoalStatus::default(),
        ),
    ]);
    s
}

/// `instance HasFrees System`'s fold (System.hs:1836-1849) over the record at
/// System.hs:383-395: the ten variable-bearing fields in declaration order,
/// each `Data.Set` / `Data.Map` field in its container order rather than in
/// the port's insertion order.  `old_neg_subterms` and the domain-only rule
/// for the equation store's disjunctions show up as the two gaps in the
/// sequence.
#[test]
fn for_each_free_walks_fields_in_system_hs_order() {
    let s = one_variable_per_field_system();
    assert_eq!(
        frees_list(&s),
        vec![
            // sNodes: ascending NodeId, each id before its rule's variables.
            nvar(10),
            mvar(11),
            nvar(20),
            mvar(21),
            // sEdges: source before target, atoms in `Ord Edge` order.
            nvar(30),
            nvar(31),
            nvar(32),
            nvar(33),
            // sLessAtoms: smaller before larger, atoms in `Ord LessAtom` order.
            nvar(40),
            nvar(41),
            nvar(42),
            nvar(43),
            // sLastAtom.
            nvar(50),
            // sSubtermStore: negative, then positive, then solved; the two
            // `Vec`-backed halves by `(small, big)`.  `old_neg_subterms`
            // (x.98, x.99) is not walked.
            mvar(90),
            mvar(91),
            mvar(70),
            mvar(71),
            mvar(72),
            mvar(73),
            mvar(80),
            mvar(81),
            // sEqStore: the free substitution's keys and ranges in ascending
            // key order, then the disjunctions — each in `Ord LNSubstVFresh`
            // order and contributing its DOMAIN only, so x.111 and x.113 are
            // not walked.
            mvar(100),
            mvar(101),
            mvar(102),
            mvar(103),
            mvar(110),
            mvar(112),
            // sFormulas, sSolvedFormulas, sLemmas: each store by `Ord Guarded`.
            nvar(120),
            nvar(121),
            nvar(130),
            nvar(140),
            // sGoals: ascending `Ord Goal`, so the Action goal precedes the
            // Chain one that is stored first.
            nvar(150),
            mvar(151),
            nvar(160),
            nvar(161),
        ]
    );
}

/// `instance HasFrees System`'s map (System.hs:1866-1879) rebuilds each
/// `Vec`-backed field where it stands, where HS re-establishes the container
/// with `S.fromList` / `M.fromList` (LTerm.hs:903, LTerm.hs:914).  The ranges
/// of the equation store's disjunctions and `old_neg_subterms` are carried
/// over untouched.
#[test]
fn map_free_keeps_storage_order_and_conj_ranges() {
    let mapped = one_variable_per_field_system()
        .map_free(&mut |v: LVar| LVar::new(v.name, v.sort, v.idx + 1000));
    let node_ids: Vec<u64> = mapped.nodes.iter().map(|(id, _)| id.idx).collect();
    assert_eq!(node_ids, vec![1020, 1010]);
    let edge_srcs: Vec<u64> = mapped.edges.iter().map(|e| e.src.0.idx).collect();
    assert_eq!(edge_srcs, vec![1032, 1030]);
    let less: Vec<u64> = mapped.less_atoms.iter().map(|l| l.smaller.idx).collect();
    assert_eq!(less, vec![1042, 1040]);
    assert_eq!(
        *mapped.formulas[0],
        last_formula(1121),
        "the formula store keeps its insertion order"
    );
    assert!(
        matches!(mapped.goals[0].0, Goal::Chain(..)),
        "the goal store keeps its insertion order"
    );
    let subterms: Vec<u64> = mapped
        .subterm_store
        .subterms
        .iter()
        .map(|c| match &c.small {
            Term::Lit(Lit::Var(v)) => v.idx,
            _ => unreachable!("the fixture stores variable terms"),
        })
        .collect();
    assert_eq!(subterms, vec![1072, 1070]);
    assert!(
        mapped.subterm_store.subterms.iter().all(|c| c.propagated),
        "the propagated marker is carried over"
    );
    assert_eq!(
        mapped.subterm_store.old_neg_subterms,
        SortedPairSet::rebuild_from(vec![(mterm(98), mterm(99))])
    );
    assert_eq!(
        mapped.eq_store.conj[0].substs[0].to_list(),
        vec![(mvar(1110), mterm(111))],
        "a disjunction rebuilds set order while keeping its ranges"
    );
}

/// The map's epilogue: both max-var-idx caches are invalidated (a rewrite may
/// LOWER a maximum, and a stale-high cache would seed fresh indices above the
/// ones Haskell picks) and every stamp is fresh, so no inherited no-op verdict
/// survives.
#[test]
fn map_free_mints_stamps_and_invalidates_both_caches() {
    use crate::constraint::solver::reduction::{bounds_max, bounds_max_uncached};
    let s = one_variable_per_field_system();
    // Populate both caches with the pre-map maximum, and set the marker.
    let before = bounds_max(&s);
    assert!(s.max_var_idx_cache.get().is_some());
    assert!(s.node_max_cache.get().is_some());
    s.record_subst_marker();
    let content_stamp = s.content_stamp.get();
    let subst_stamp = s.subst_stamp.get();

    let mapped = s.map_free(&mut |v: LVar| LVar::new(v.name, v.sort, v.idx - 5));
    assert!(mapped.max_var_idx_cache.get().is_none());
    assert!(mapped.node_max_cache.get().is_none());
    assert_ne!(mapped.content_stamp.get(), content_stamp);
    assert_ne!(mapped.subst_stamp.get(), subst_stamp);
    assert!(mapped.subst_applied_marker.get().is_none());

    let uncached = bounds_max_uncached(&mapped);
    assert!(uncached < before, "the rename lowers the maximum");
    assert_eq!(
        bounds_max(&mapped),
        uncached,
        "a stale cache would report {before}"
    );
}

/// `bounds_max` (reduction.rs) is a hand-written twin of this fold, kept for
/// its static dispatch on the solver's hot path.  Lifting any one variable the
/// instance walks above all the others lifts the twin's maximum with it, so
/// the two cover the same fields.  A disjunction goal is the exception the
/// twin makes on purpose: the variables under a disjunction do not raise the
/// fresh-index floor.
#[test]
fn bounds_max_covers_every_field_except_disj_goals() {
    use crate::constraint::solver::reduction::bounds_max_uncached;
    const ABOVE_ALL: u64 = 10_000;
    let walked = frees(&one_variable_per_field_system());
    for v in &walked {
        let bumped = one_variable_per_field_system().map_free(&mut |w: LVar| {
            if w == *v {
                LVar::new(w.name, w.sort, ABOVE_ALL)
            } else {
                w
            }
        });
        assert_eq!(
            bounds_max_uncached(&bumped),
            ABOVE_ALL,
            "the twin does not reach {v:?}"
        );
    }

    let top = walked.last().expect("the fixture carries variables").idx;
    let mut with_disj = one_variable_per_field_system();
    let mut goals = (*with_disj.goals).clone();
    goals.push((
        Goal::Disj(Disj::new(vec![last_formula(ABOVE_ALL)])),
        GoalStatus::default(),
    ));
    with_disj.content_mut().goals = Arc::new(goals);
    assert!(
        frees_list(&with_disj).contains(&nvar(ABOVE_ALL)),
        "the instance reaches a disjunction goal's formulas"
    );
    assert_eq!(
        bounds_max_uncached(&with_disj),
        top,
        "the twin skips a disjunction goal"
    );
}

/// HS derives `Ord GoalStatus` over `_gsSolved`, `_gsNr`, `_gsLoopBreaker`
/// (System.hs:369-379).  The port declares `looping` first, so a pair whose
/// `solved` and `looping` disagree in opposite directions settles on
/// `solved`.
#[test]
fn goal_status_ord_follows_the_hs_field_order() {
    let looping_and_unsolved = GoalStatus {
        looping: true,
        solved: false,
        nr: 0,
    };
    let solved_and_not_looping = GoalStatus {
        looping: false,
        solved: true,
        nr: 0,
    };
    assert_eq!(
        looping_and_unsolved.cmp(&solved_and_not_looping),
        std::cmp::Ordering::Less
    );
}
