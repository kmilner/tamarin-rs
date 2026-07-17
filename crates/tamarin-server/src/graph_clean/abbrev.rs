//! Node abbreviation (BEHAVIOR.md §5): assigning short NAMES to complex terms
//! and rendering the legend table.
//!
//! Four things here are determined by observation and tested:
//!   * [`prefix_for_symbol`] — the `PREFIX` derivation,
//!   * [`Abbreviator`] — per-prefix sequential numbering + nesting substitution,
//!   * [`legend_html`] — the exact `<TABLE …>` bytes incl. the 65-space hang indent,
//!   * [`select`] — the SELECTION rule: abbreviate a sub-term iff its rendered
//!     length ≥ 10 and it occurs ≥ 2 times and it is not a tuple (§5c). Both
//!     necessary gates are corpus-exact (0 counterexamples / 97 538 abbreviations)
//!     and each was confirmed by a controlled black-box probe.
//!
//! The remaining gaps are the canonical numbering tie-break (§5b; the caller
//! controls insertion order) and, for DH/AC sub-terms, whose occurrences tamarin
//! counts over a normalised form (§5c residual).

use std::collections::HashMap;

use super::term::Term;

/// The opening tag of every legend table. Its byte length is the hang-indent
/// applied to continuation `<TR>` rows.
pub const TABLE_OPEN: &str =
    "<TABLE BORDER=\"1\" CELLBORDER=\"0\" CELLSPACING=\"3\" CELLPADDING=\"1\">";

/// `PREFIX` for an abbreviation name: the first two *alphabetic* characters of
/// `name`, uppercased (one char if only one letter exists). Non-letters (digits,
/// `_`, `.`) are skipped. This is applied to the root symbol's *name* — for a
/// function `f(..)` that is `f`; for a constant `'c'` it is `c`; for a variable
/// `~v`/`$v`/`v` it is `v`; for an infix operator it is the operator's function
/// name (see [`Term::root_symbol_name`], which maps `^`→`exp`, `*`→`mult`,
/// `++`→`union`, `⊕`→`xor`).
///
/// Examples (all observed): `sign`→`SI`, `senc`→`SE`, `hash`→`HA`, `h2`→`H`,
/// `KDF`→`KD`, `pk`→`PK`, `aenc`→`AE`, `exp`→`EX`, `mult`→`MU`, `union`→`UN`,
/// `xor`→`XO`, `uninitialized`→`UN`, `F_status`→`FS`, `AMF_UE_NGAP_ID`→`AM`.
pub fn prefix_for_symbol(name: &str) -> String {
    name.chars()
        .filter(|c| c.is_ascii_alphabetic())
        .take(2)
        .flat_map(|c| c.to_uppercase())
        .collect()
}

/// Assigns and remembers abbreviation names, de-duplicating identical terms and
/// numbering `1,2,3,…` per prefix in the order terms are [`Abbreviator::add`]ed.
///
/// Numbering order matches tamarin only where the canonical order is
/// unambiguous (see BEHAVIOR.md §5b); the caller decides insertion order.
#[derive(Default)]
pub struct Abbreviator {
    /// name -> the term it stands for, in insertion order.
    entries: Vec<(String, Term)>,
    /// canonical fully-expanded key -> assigned name (dedup).
    by_key: HashMap<String, String>,
    /// prefix -> next counter value.
    counters: HashMap<String, u32>,
}

impl Abbreviator {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register `term` for abbreviation, returning its name. Terms that render
    /// identically (fully expanded) share one name.
    pub fn add(&mut self, term: Term) -> String {
        let key = term.render_full();
        if let Some(existing) = self.by_key.get(&key) {
            return existing.clone();
        }
        let prefix = prefix_for_symbol(&term.root_symbol_name());
        let n = self.counters.entry(prefix.clone()).or_insert(0);
        *n += 1;
        let name = format!("{}{}", prefix, n);
        self.by_key.insert(key, name.clone());
        self.entries.push((name.clone(), term));
        name
    }

    /// The name for an already-registered term, if any (by full rendering).
    pub fn name_of(&self, term: &Term) -> Option<&str> {
        self.by_key.get(&term.render_full()).map(String::as_str)
    }

    /// Legend rows `(name, expansion)` in insertion order. Each expansion renders
    /// the term one level with any registered *sub*-term replaced by its name
    /// (nesting, §5b: `EX1 = 'g'^MU1`). The expansion string is NOT yet
    /// HTML-escaped; [`legend_html`] escapes it.
    pub fn rows(&self) -> Vec<(String, String)> {
        self.entries
            .iter()
            .map(|(name, term)| (name.clone(), term.render_abbrev(&self.by_key)))
            .collect()
    }

    /// Render the legend as the exact inner HTML of the `plain` node's label
    /// (the bytes between `label=<` and `>`). Empty if no entries.
    pub fn legend_html(&self) -> String {
        legend_html(&self.rows())
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
    pub fn len(&self) -> usize {
        self.entries.len()
    }
}

/// HTML-escape a legend expansion: `&`→`&amp;`, `<`→`&lt;`, `>`→`&gt;`. Single
/// quotes and `* ^ ~ $ ⊕ ++` are left literal (as observed).
pub fn escape_expansion(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            _ => out.push(c),
        }
    }
    out
}

/// Render one legend row's `<TR>…</TR>` (expansion is escaped here).
fn legend_row(name: &str, expansion: &str) -> String {
    format!(
        "<TR><TD ALIGN=\"LEFT\" VALIGN=\"TOP\"><FONT COLOR=\"#000000\">{}</FONT></TD> <TD ALIGN=\"LEFT\" VALIGN=\"TOP\">=</TD> <TD ALIGN=\"LEFT\" VALIGN=\"TOP\">{}</TD></TR>",
        name,
        escape_expansion(expansion),
    )
}

/// The exact inner HTML for the legend `plain` node (between `label=<` and `>`):
/// `<TABLE …><TR>row0</TR>\n<65sp><TR>row1</TR>\n…<65sp><TR>rowN</TR></TABLE>`.
/// The first row is inline after the table tag; every continuation row is on its
/// own line indented by `TABLE_OPEN.len()` (= 65) spaces.
pub fn legend_html(rows: &[(String, String)]) -> String {
    if rows.is_empty() {
        return String::new();
    }
    let indent = " ".repeat(TABLE_OPEN.len());
    let mut s = String::new();
    s.push_str(TABLE_OPEN);
    for (i, (name, exp)) in rows.iter().enumerate() {
        if i > 0 {
            s.push('\n');
            s.push_str(&indent);
        }
        s.push_str(&legend_row(name, exp));
    }
    s.push_str("</TABLE>");
    s
}

/// Minimum fully-expanded rendered length for a sub-term to be abbreviated.
/// Corpus-exact: the shortest of 97 538 legend expansions is 10 chars, none is 9;
/// live probe: `'12345678'` (10) is abbreviated, `'1234567'` (9) is not.
pub const MIN_ABBREV_LEN: usize = 10;
/// Minimum occurrence count for a sub-term to be abbreviated. Live probe: a
/// 12-char term is abbreviated at 2 occurrences, a 42-char term is NOT at 1.
pub const MIN_ABBREV_OCC: usize = 2;

/// Select which sub-terms of `roots` to abbreviate (BEHAVIOR.md §5c).
///
/// **The rule** (each gate confirmed independently by controlled black-box
/// probes; both necessary gates are corpus-exact with 0 counterexamples over
/// 97 538 abbreviations): a sub-term `t` is abbreviated **iff**
///  1. `t.render_len() >= MIN_ABBREV_LEN` (10),
///  2. `t` occurs `>= MIN_ABBREV_OCC` (2) times across `roots`, and
///  3. `t` is not a tuple/pair.
///
/// Atoms are eligible (a long constant/variable is abbreviated). Selection is
/// bottom-up (shortest first) so nested eligible sub-terms are named before the
/// terms that contain them (`LO1='longarg123'` before `H1='h(LO1)'`).
///
/// `roots` must be the full multiset of constraint-system terms (graph node-fact
/// arguments **and** the sequent's terms) — occurrence is a whole-system count,
/// not a per-drawn-node count. See BEHAVIOR.md §5c for the one documented
/// residual: for DH-exponentiation / AC-operator (`^ * ⊕ ++`) sub-terms tamarin
/// counts occurrences over the *normalised* term, which this structural count
/// does not model, so those may be over- or under-selected.
pub fn select(roots: &[Term]) -> Vec<Term> {
    select_with(roots, MIN_ABBREV_LEN, MIN_ABBREV_OCC)
}

/// [`select`] with explicit thresholds (for probing / tests).
pub fn select_with(roots: &[Term], min_len: usize, min_occ: usize) -> Vec<Term> {
    let mut counts: HashMap<String, (usize, Term)> = HashMap::new();
    for r in roots {
        r.for_each_subterm(&mut |t| {
            if t.is_tuple() || t.render_len() < min_len {
                return;
            }
            let e = counts.entry(t.render_full()).or_insert((0, t.clone()));
            e.0 += 1;
        });
    }
    let mut picked: Vec<Term> = counts
        .into_values()
        .filter(|(c, _)| *c >= min_occ)
        .map(|(_, t)| t)
        .collect();
    // bottom-up: shortest rendering first so inner names are assigned before outer.
    picked.sort_by(|a, b| {
        a.render_len().cmp(&b.render_len()).then_with(|| a.render_full().cmp(&b.render_full()))
    });
    picked
}
