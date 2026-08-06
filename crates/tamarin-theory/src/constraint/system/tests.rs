use super::*;
use crate::fact::LNFact;
use tamarin_term::lterm::{LSort, LVar};

#[test]
fn empty_system_is_default() {
    let s = System::empty();
    assert!(s.nodes.is_empty());
    assert!(s.edges.is_empty());
    assert!(s.goals.is_empty());
}

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
        "freshen_system",
        "freshen_system_keep_with_shift",
        "freshen_system_some_inst",
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
    // Out-of-line test modules — `#[cfg(test)]` + `mod <name>;` in a parent
    // `foo.rs` puts the module's code in `foo/<name>.rs` — are whole files of
    // test code; collect them so the scan below skips them entirely.
    let mut test_files: tamarin_utils::FastSet<std::path::PathBuf> =
        tamarin_utils::FastSet::default();
    for path in &files {
        let src = std::fs::read_to_string(path).expect("read source");
        let mut lines = src.lines().peekable();
        while let Some(line) = lines.next() {
            if line.trim_start() == "#[cfg(test)]" {
                if let Some(name) = lines
                    .peek()
                    .and_then(|n| n.trim_start().strip_prefix("mod "))
                    .and_then(|r| r.strip_suffix(';'))
                {
                    test_files.insert(path.with_extension("").join(format!("{name}.rs")));
                }
            }
        }
    }
    for path in &files {
        if test_files.contains(path) {
            continue;
        }
        {
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
                if call_needles.iter().any(|n| line.contains(n))
                    && !ALLOWED.contains(&cur_fn.as_str())
                {
                    offenders.push(format!("{} in fn {}", path.display(), cur_fn));
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
                    if next != Some('.') && !ESCAPE_ALLOWED.contains(&cur_fn.as_str()) {
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

#[test]
fn insert_lemma_flattens_top_level_conj() {
    let mut s = System::empty();
    // Use Atom-bearing lemmas so the smart Conj flattening doesn't
    // optimise them away. We just need two leaves that don't
    // recurse further into Conj.
    use tamarin_parser::ast::{Atom, SortHint, Term, VarSpec};
    let mkvar = |n: &str| {
        Term::Var(VarSpec {
            name: n.to_string(),
            idx: 0,
            sort: SortHint::Node,
            typ: None,
        })
    };
    let l1 =
        crate::guarded::Guarded::Atom(crate::guarded::atom_to_gatom_free(&Atom::Last(mkvar("i"))));
    let l2 =
        crate::guarded::Guarded::Atom(crate::guarded::atom_to_gatom_free(&Atom::Last(mkvar("j"))));
    s.insert_lemma(crate::guarded::Guarded::Conj(
        vec![l1.clone(), l2.clone()].into(),
    ));
    assert_eq!(s.lemmas.len(), 2);
    assert!(crate::guarded::stores_contains(&s.lemmas, &l1));
    assert!(crate::guarded::stores_contains(&s.lemmas, &l2));
}

#[test]
fn formula_to_system_exists_trace_keeps_formula() {
    use tamarin_parser::ast::TraceQuantifier;
    let f = crate::guarded::gtrue();
    let sys = formula_to_system(
        Vec::new(),
        SourceKind::RawSources,
        TraceQuantifier::ExistsTrace,
        false,
        &f,
    );
    // ExistsTrace ⇒ formula kept as-is.
    assert_eq!(sys.formulas.len(), 1);
    assert_eq!(*sys.formulas[0], f);
}

#[test]
fn formula_to_system_all_traces_negates() {
    use tamarin_parser::ast::TraceQuantifier;
    // For AllTraces lemma `T`, the negation is `gfalse`.
    let f = crate::guarded::gtrue();
    let sys = formula_to_system(
        Vec::new(),
        SourceKind::RawSources,
        TraceQuantifier::AllTraces,
        false,
        &f,
    );
    assert_eq!(sys.formulas.len(), 1);
    assert_eq!(*sys.formulas[0], crate::guarded::gfalse());
}

#[test]
fn formula_to_system_partitions_safety_restrictions() {
    use tamarin_parser::ast::TraceQuantifier;
    let f = crate::guarded::gtrue();
    // gtrue is safety (no Ex, no free vars).
    // gfalse is also safety (Disj([])) — no Ex, no free vars.
    let restrictions = vec![crate::guarded::gtrue(), crate::guarded::gfalse()];
    let sys = formula_to_system(
        restrictions,
        SourceKind::RawSources,
        TraceQuantifier::ExistsTrace,
        false,
        &f,
    );
    // All restrictions are safety → all go into lemmas.
    assert_eq!(sys.formulas.len(), 1);
    // gtrue is `Conj []` which `insert_lemma` flattens to nothing
    // (no items inside the empty conjunction). gfalse stays.
    // Lemmas should contain at least the gfalse non-conj entry.
    assert!(crate::guarded::stores_contains(
        &sys.lemmas,
        &crate::guarded::gfalse()
    ));
}
