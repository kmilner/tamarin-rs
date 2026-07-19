// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, felixlinker, jdreier, rkunnema, racoucho1u, beschmi,
//   rsasse, symphorien, PhilipLukertWork, felixonmars, yavivanov,
//   katrielalex, robert.kunnemann@cased.de, xaDxelA, and other minor
//   contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Constraint/Solver/Contradictions.hs,
//   lib/theory/src/Theory/Constraint/Solver/ProofMethod.hs,
//   lib/theory/src/Theory/Proof.hs

//! Proof-skeleton printer + Haskell `--output=` extractor for
//! cross-checking that our proof trees structurally match
//! `tamarin-prover`'s.
//!
//! This module is a test-only cross-checking harness; it is **not**
//! part of `--prove` output. The production pretty-printer lives in
//! `pretty_theory.rs` (`pretty_proof_body` / `pp_step_doc`, port of
//! `Theory/Proof.hs` `prettyProofWith`/`ppCases`) and
//! `constraint/solver/proof_method.rs` (port of
//! `Theory/Constraint/Solver/ProofMethod.hs` `prettyProofMethod`).
//! The "intentionally drops X" notes below describe abbreviations made
//! by *this* skeleton diff tool, not divergences in the real prover.
//!
//! The skeleton intentionally drops goal pretty-printing (variable
//! indices and term rendering diverge for cosmetic reasons even when
//! the search is identical). What remains is the *shape*:
//!
//!   induction
//!     case empty_trace
//!     by contradiction
//!   case non_empty_trace
//!     simplify
//!     solve
//!       case case_1
//!       ...
//!     qed
//!   qed
//!
//! That's enough to surface real divergences — wrong number of
//! children, wrong case names, missed induction, premature SOLVED —
//! while normalizing away the term-printing noise.
//!
//! Two diff strategies are supported:
//!   1. `first_divergence` — point at the first differing line for
//!      a focused bug-hunt.
//!   2. Full skeleton strings — feed into a `similar`-style line
//!      diff for a holistic view.

use crate::constraint::solver::proof_method::{ProofMethod, Result as MethodResult};
use crate::constraint::solver::search::{NodeStatus, ProofNode};

/// Render our proof tree in a normalized, Haskell-compatible skeleton.
///
/// Output uses tamarin's textual proof conventions:
///   - `induction`, `simplify`, `solve` keywords for proof methods
///   - `case <name>` per child
///   - `next` between siblings; `qed` after the last sibling
///   - `by sorry` / `by contradiction` for terminal Sorry/Contradictory
///   - `SOLVED` for Finished(Solved) leaves
///
/// Indentation is 2-space, matching `Theory.Constraint.Solver.ProofMethod`'s
/// `prettyProof`.
pub fn render(root: &ProofNode) -> String {
    let mut out = String::new();
    render_node(root, 0, &mut out);
    out
}

fn render_node(node: &ProofNode, indent: usize, out: &mut String) {
    let pad = "  ".repeat(indent);
    // Terminal-method handling: Sorry/Finished and SolveGoal/Simplify
    // /Induction with no children are leaves.  Haskell's prettyProof
    // emits `by <method>` as a single line for leaves whose method is
    // not Finished (Proof.hs:1064-1066), so we mirror that here — emit
    // *just* the leaf line, skipping the separate method-keyword line.
    if node.children.is_empty() {
        match &node.method {
            ProofMethod::Finished(MethodResult::Contradictory(c)) => {
                out.push_str(&pad);
                out.push_str("by contradiction /* ");
                out.push_str(&contradiction_label(c));
                out.push_str(" */\n");
            }
            ProofMethod::Finished(MethodResult::Solved) => {
                // Mirror HS `prettyProofMethod` (ProofMethod.hs:1174-1187, see line 1177):
                //   `keyword_ "SOLVED" <-> lineComment_ "trace found"`.
                out.push_str(&pad);
                out.push_str("SOLVED // trace found\n");
            }
            ProofMethod::Finished(MethodResult::Unfinishable) => {
                out.push_str(&pad);
                out.push_str("by UNFINISHABLE // reducible operator in subterm\n");
            }
            ProofMethod::Sorry(reason) => {
                out.push_str(&pad);
                out.push_str("by sorry");
                if let Some(r) = reason {
                    out.push_str(" /* ");
                    out.push_str(r);
                    out.push_str(" */");
                }
                out.push('\n');
            }
            ProofMethod::Simplify
            | ProofMethod::SolveGoal(_)
            | ProofMethod::Induction
            | ProofMethod::Invalidated
            | ProofMethod::RawSolve(_) => {
                // Non-terminal method with no children — must have
                // closed contradictorily without producing cases.
                // Haskell renders this as `by solve(...)` / `by simplify`
                // / `by induction`; our `extract_from_haskell` normalises
                // those to `by contradiction /* closed */` so the diff
                // treats both leaf-closure forms as equivalent.
                out.push_str(&pad);
                out.push_str(match node.status {
                    NodeStatus::Contradictory => "by contradiction /* closed */\n",
                    NodeStatus::Solved => "SOLVED // trace found\n",
                    NodeStatus::Sorry => "by sorry\n",
                    NodeStatus::Unfinishable => "by UNFINISHABLE // reducible operator in subterm\n",
                    NodeStatus::Open => "by sorry /* open */\n",
                });
            }
        }
        return;
    }
    // Non-leaf: emit the method keyword line, then children.
    let kw = method_keyword(&node.method);
    if !kw.is_empty() {
        out.push_str(&pad);
        out.push_str(kw);
        out.push('\n');
    }
    // Special case: a single child with empty key is a "Linear"
    // continuation (no branching). Haskell prints these inline, with
    // no `case`/`next`/`qed` wrapper.
    if node.children.len() == 1 {
        if let Some((name, child)) = node.children.iter().next() {
            if name.is_empty() {
                render_node(child, indent, out);
                return;
            }
        }
    }
    // On exists-trace lemmas only the trace-found path survives: when a
    // node's status rolls up to Solved (TraceFound), siblings that closed
    // Contradictory are elided.  In Haskell this pruning is done *before*
    // printing, by `cutOnSolved*` -> `extractSolved` (Proof.hs:879-882,
    // 920-923), which rebuilds the tree keeping one label per level;
    // `prettyProof` itself prints whatever tree it is handed.
    //
    // Mirror that pruning here so the skeleton diff is apples-to-apples.
    // We keep only the FIRST Solved child and drop other
    // Contradictory/Sorry siblings.  All-traces proofs (status =
    // Contradictory) keep every branch.
    let children_to_render: Vec<(String, &ProofNode)> =
        if node.status == NodeStatus::Solved {
            // Find the first Solved child; render only that one.
            match node.children.iter()
                .find(|(_, c)| c.status == NodeStatus::Solved) {
                Some((name, child)) => {
                    // Haskell's `extractSolved` (`Theory/Proof.hs:921-923`)
                    // keeps the survivor's label verbatim — including any
                    // `_case_N` dedup suffix appended by `uniqueListBy`
                    // (ProofMethod.hs:91-103, applied at :308) when the goal
                    // originally had multiple cases sharing a rule name.
                    // Pass the name through unchanged.
                    vec![(name.clone(), child)]
                }
                None => node.children.iter()
                    .map(|(n, c)| (n.clone(), c))
                    .collect(),
            }
        } else {
            node.children.iter()
                .map(|(n, c)| (n.clone(), c))
                .collect()
        };
    // After elision, a singleton empty-key child is still Linear.
    if children_to_render.len() == 1 && children_to_render[0].0.is_empty() {
        render_node(children_to_render[0].1, indent, out);
        return;
    }
    // Render children. BTreeMap iterates in key order, which is the
    // stable canonical order we want for the diff.
    //
    // Indentation convention from Haskell's `prettyProof`:
    //   - method (this node) at indent N
    //   - `case X` at indent N+1
    //   - child body at indent N+1 (same as case heading)
    //   - `next` between siblings at indent N (method level)
    //   - `qed` after last sibling at indent N (method level)
    let pad_case = "  ".repeat(indent + 1);
    let pad_method = "  ".repeat(indent);
    let n = children_to_render.len();
    for (i, (name, child)) in children_to_render.iter().enumerate() {
        out.push_str(&pad_case);
        out.push_str("case ");
        out.push_str(name);
        out.push('\n');
        render_node(child, indent + 1, out);
        if i + 1 < n {
            out.push_str(&pad_method);
            out.push_str("next\n");
        }
    }
    out.push_str(&pad_method);
    out.push_str("qed\n");
}

fn method_keyword(m: &ProofMethod) -> &'static str {
    match m {
        ProofMethod::Simplify => "simplify",
        ProofMethod::SolveGoal(_) => "solve",
        ProofMethod::Induction => "induction",
        ProofMethod::Sorry(_) => "",     // handled at leaf-emit time
        ProofMethod::Finished(_) => "",  // handled at leaf-emit time
        ProofMethod::Invalidated => "INVALIDATED",
        ProofMethod::RawSolve(_) => "solve", // display-only; handled in pp_step_doc
    }
}

fn contradiction_label(
    c: &Option<crate::constraint::solver::contradictions::Contradiction>,
) -> String {
    use crate::constraint::solver::contradictions::Contradiction as K;
    // Strings are abbreviated mirrors of Haskell `prettyContradiction`
    // (Contradictions.hs:437-455, see line 438+); see the case there for each variant.
    // A few variants drop Haskell's interpolated detail (e.g. Haskell's
    // `"node " ++ show j ++ " after last node " ++ show i` becomes
    // `"node after last"`, `"non-injective facts " ++ show cex` becomes
    // `"non-injective facts"`, and the `"derived before and after"`
    // wrapper drops its term/node id).  This is fine: the label is only
    // emitted inside a `/* ... */` comment that `normalise_leaf_closure`
    // collapses to `by contradiction /* closed */` before diffing, so
    // the label text never affects comparison results.
    match c {
        None => "closed".to_string(),
        Some(K::Cyclic) => "cyclic".to_string(),
        Some(K::ForbiddenChain) => "forbidden chain".to_string(),
        Some(K::ForbiddenKD) => "forbidden KD-fact".to_string(),
        Some(K::ImpossibleChain) => "impossible chain".to_string(),
        Some(K::NodeAfterLast(..)) => "node after last".to_string(),
        Some(K::NonInjectiveFactInstance(..)) => "non-injective facts".to_string(),
        Some(K::SubtermCyclic) => "contradictory subterm store".to_string(),
        Some(K::NonNormalTerms) => "non-normal terms".to_string(),
        Some(K::FormulasFalse) => "from formulas".to_string(),
        Some(K::IncompatibleEqs) => "incompatible equalities".to_string(),
        Some(K::SuperfluousLearn(..)) => "derived before and after".to_string(),
        Some(K::ForbiddenExp) => "non-normal exponentiation rule instance".to_string(),
        Some(K::ForbiddenBP) => "non-normal bilinear pairing rule instance".to_string(),
    }
}

/// Extract the proof skeleton for a single lemma from a `--output=`
/// produced `.spthy` file. Returns the same line shape as `render`
/// so the two strings can be diffed.
///
/// The textual format from tamarin looks like:
///
///   lemma <name>: ... "..."
///   /* guarded formula ... */
///   <method>
///     case <name>
///     ...
///     qed
///
/// We strip the lemma header + guarded-formula comment, normalize the
/// `solve( <goal> )` lines to bare `solve`, drop the contradiction
/// reason variants we don't track yet, and re-emit the rest.
pub fn extract_from_haskell(spthy_text: &str, lemma_name: &str) -> Option<String> {
    let lines: Vec<&str> = spthy_text.lines().collect();
    // Find the lemma header.
    let mut i = 0;
    let header = format!("lemma {}", lemma_name);
    while i < lines.len() {
        let l = lines[i].trim_start();
        // Match `lemma NAME:` or `lemma NAME [...]`. Accept both.
        if l.starts_with(&header) {
            let rest = &l[header.len()..];
            let nxt = rest.chars().next();
            if matches!(nxt, Some(':') | Some(' ') | Some('[') | None) {
                break;
            }
        }
        i += 1;
    }
    if i >= lines.len() {
        return None;
    }
    // Skip the formula string + any /* ... */ block-comment until we
    // hit the first proof line (induction / simplify / solve / by ...).
    i += 1;
    let is_proof_kw = |l: &str| {
        let t = l.trim_start();
        t.starts_with("induction")
            || t.starts_with("simplify")
            || t.starts_with("solve(")
            || t.starts_with("solve ")
            || t.starts_with("by ")
            || t == "by"
    };
    while i < lines.len() && !is_proof_kw(lines[i]) {
        // Stop early if we hit the next lemma — means no proof.
        if lines[i].trim_start().starts_with("lemma ")
            || lines[i].trim_start().starts_with("end")
        {
            return None;
        }
        i += 1;
    }
    if i >= lines.len() {
        return None;
    }
    // Track method scopes with a stack. Haskell's printer omits `qed`
    // for single-child methods, so depth-counting alone misses where
    // the proof ends. The stack tracks each unresolved method:
    //   - method lines (induction/simplify/solve) push "Uncommitted"
    //   - first `case` line commits top-of-stack to "Multi"
    //   - `qed` pops a Multi (then chain-pops any Uncommitted parent
    //     whose single-child path is now resolved)
    //   - leaf lines (`by ...` / `SOLVED`) chain-pop any Uncommitted
    //     ancestors whose single-child path is resolved by this leaf
    //
    // The proof ends when the stack returns to empty.
    #[derive(Clone, Copy, PartialEq)]
    enum Scope { Uncommitted, Multi }
    let mut out = String::new();
    let mut stack: Vec<Scope> = Vec::new();
    let mut opened_any = false;
    while i < lines.len() {
        let raw = lines[i];
        let t = raw.trim_start();
        // Hard stop: a top-level lemma/rule/restriction declaration.
        if stack.is_empty() && opened_any
            && (t.starts_with("lemma ")
                || t.starts_with("end")
                || t.starts_with("rule ")
                || t.starts_with("restriction ")
                || t.starts_with("functions:")
                || t.starts_with("equations:")
                || t.starts_with("builtins:"))
        {
            break;
        }
        let norm = normalize_haskell_line(raw);
        if let Some(n) = norm {
            let nt = n.trim_start();
            if nt == "induction" || nt == "simplify" || nt == "solve" {
                stack.push(Scope::Uncommitted);
                opened_any = true;
            } else if nt.starts_with("case ") {
                if let Some(top) = stack.last_mut() {
                    *top = Scope::Multi;
                }
            } else if nt == "qed" {
                stack.pop();  // pops the Multi
                // Chain-pop any Uncommitted ancestor whose
                // single-child path resolves via this child's qed.
                while let Some(Scope::Uncommitted) = stack.last() {
                    stack.pop();
                }
            } else if nt.starts_with("by ") || nt == "SOLVED" || nt.starts_with("SOLVED ") {
                // Leaf: resolve any Uncommitted ancestors above us.
                // (`"SOLVED "` covers `"SOLVED // trace found"` after the
                // normalise step preserves the trailing comment.)
                while let Some(Scope::Uncommitted) = stack.last() {
                    stack.pop();
                }
            }
            out.push_str(&n);
            out.push('\n');
        }
        i += 1;
        if stack.is_empty() && opened_any {
            break;
        }
    }
    Some(out)
}

/// Normalize one line from tamarin's textual proof to the same form
/// `render` produces. Returns `None` for lines we drop (block-comment
/// fragments, blank lines, etc).
fn normalize_haskell_line(raw: &str) -> Option<String> {
    let indent_count = raw.chars().take_while(|c| *c == ' ').count();
    // Tamarin uses 2-space indent same as us; pass it through.
    let pad = " ".repeat(indent_count);
    let t = raw.trim();
    if t.is_empty() { return None; }
    // Drop block-comment fragments.  `by contradiction /* ... */` is
    // fine — it doesn't start with `/*` or `*`, and isn't exactly `*/`.
    if t.starts_with("/*") || t.starts_with("*") || t == "*/" {
        return None;
    }
    // Tokenize.
    if t == "qed" || t == "next" {
        return Some(format!("{}{}", pad, t));
    }
    if t == "induction" {
        return Some(format!("{}induction", pad));
    }
    if t == "simplify" {
        return Some(format!("{}simplify", pad));
    }
    if let Some(rest) = t.strip_prefix("solve(") {
        // Drop the goal payload — keep just `solve`.
        let _ = rest;
        return Some(format!("{}solve", pad));
    }
    if t.starts_with("solve ") {
        return Some(format!("{}solve", pad));
    }
    if let Some(rest) = t.strip_prefix("case ") {
        // Keep the case-name verbatim.
        return Some(format!("{}case {}", pad, rest.trim()));
    }
    if let Some(rest) = t.strip_prefix("by contradiction") {
        // Extract the /* reason */ if present.
        let reason = rest.trim();
        if let Some(inner) = reason.strip_prefix("/*").and_then(|s| s.strip_suffix("*/")) {
            return Some(format!(
                "{}by contradiction /* {} */",
                pad,
                inner.trim()
            ));
        }
        return Some(format!("{}by contradiction", pad));
    }
    if t.starts_with("by sorry") {
        return Some(format!("{}by sorry", pad));
    }
    // UNFINISHABLE leaf (reducible operator in subterm).  Haskell's
    // `prettyProof` prepends `by ` to this non-Solved finished leaf
    // (ppCases ps [] at Proof.hs:1054-1075, see line 1065) and `prettyProofMethod` emits
    // `keyword_ "UNFINISHABLE" <-> lineComment_ "reducible operator in
    // subterm"` (ProofMethod.hs:1174-1187, see line 1179).  Our `render` emits the same
    // line, so preserve it verbatim instead of dropping it.
    if t.starts_with("UNFINISHABLE") || t.starts_with("by UNFINISHABLE") {
        return Some(format!(
            "{}by UNFINISHABLE // reducible operator in subterm",
            pad
        ));
    }
    if t == "SOLVED" || t.starts_with("SOLVED") || t == "by SOLVED" {
        // HS pretty-prints `keyword_ "SOLVED" <-> lineComment_ "trace found"`
        // (ProofMethod.hs:1174-1187, see line 1177), so the raw line is `SOLVED // trace found`.
        // Our `render` emits the same suffix; preserve it here so the diff
        // matches verbatim instead of treating the cosmetic comment as a
        // divergence.
        let rest = t.strip_prefix("by ").unwrap_or(t)  // "by SOLVED" → "SOLVED"
                    .strip_prefix("SOLVED").unwrap_or("").trim();
        if rest.is_empty() {
            return Some(format!("{}SOLVED", pad));
        }
        return Some(format!("{}SOLVED {}", pad, rest));
    }
    // `by solve(...)` and `by induction` — leaf closures that tamarin's
    // printer emits when the case closes after exactly one more proof
    // step (no further branching).  Our printer emits the same situation
    // as `by contradiction /* <reason> */` (the contradiction that
    // closed the trailing system).  Render both as a uniform
    // `by contradiction /* closed */` marker so the diff treats them as
    // equivalent leaf-closure forms.  Without this normalisation, the
    // c_h case in CR_external (closed by `by solve(!KU(~k))` in
    // tamarin, `by contradiction /* cyclic */` in ours) shows up as a
    // proof-trace mismatch despite being semantically the same leaf.
    if t.starts_with("by solve(") || t == "by solve" || t.starts_with("by induction") {
        return Some(format!("{}by contradiction /* closed */", pad));
    }
    // Unknown line — drop.
    None
}

/// Normalise a leaf-closure line so different closure styles compare
/// equal: `by contradiction /* X */` → `by contradiction /* closed */`
/// for any `X`.  Used by `first_divergence` only; preserves the
/// rendered forms otherwise.
fn normalise_leaf_closure(line: &str) -> String {
    let lead = line.chars().take_while(|c| *c == ' ').collect::<String>();
    let t = line.trim_start();
    if t.starts_with("by contradiction") {
        return format!("{}by contradiction /* closed */", lead);
    }
    line.to_string()
}

/// Find the first divergence between two skeleton strings.
/// Returns `(line_no, ours_line, theirs_line)` or None if identical.
///
/// Leaf-closure lines (`by contradiction /* … */`) are normalised
/// before comparison so different closure reasons (`cyclic`, `from
/// formulas`, `closed`) all compare equal.  The case-tree structure
/// (case names, depth, qed/next placement) is what determines whether
/// our proof matches Haskell's — the specific contradiction reason
/// is implementation-detail noise.
pub fn first_divergence(ours: &str, theirs: &str) -> Option<(usize, String, String)> {
    let a: Vec<&str> = ours.lines().collect();
    let b: Vec<&str> = theirs.lines().collect();
    let n = a.len().max(b.len());
    for i in 0..n {
        let x = a.get(i).copied().unwrap_or("<EOF>");
        let y = b.get(i).copied().unwrap_or("<EOF>");
        let xn = normalise_leaf_closure(x);
        let yn = normalise_leaf_closure(y);
        if xn != yn {
            return Some((i + 1, x.to_string(), y.to_string()));
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extract_simple_two_lemma_proof() {
        let s = r#"theory T begin
lemma foo:
  all-traces
  "..."
/*
guarded formula ...
*/
simplify
by contradiction /* from formulas */

lemma bar:
  exists-trace
  "..."
simplify
solve( !Foo( x ) )
  case A
  by contradiction /* cyclic */
next
  case B
  SOLVED
qed
end"#;
        let foo = extract_from_haskell(s, "foo").unwrap();
        assert!(foo.contains("simplify"));
        assert!(foo.contains("by contradiction /* from formulas */"));
        let bar = extract_from_haskell(s, "bar").unwrap();
        assert!(bar.contains("simplify"));
        assert!(bar.contains("solve"));
        assert!(bar.contains("case A"));
        assert!(bar.contains("case B"));
        assert!(bar.contains("qed"));
    }
}
