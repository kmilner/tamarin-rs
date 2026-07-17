//! The proof-script (west) pane markup embedded in the theory-view page and in
//! the `main/*` navigation.
//!
//! ## Line model (observed)
//! The pane is a flat sequence of logical lines. Rendering emits each line's
//! text followed by the literal `"<br/>\n"`, and finally a single trailing
//! space `" "`. A blank line is an element whose text is empty (yielding a lone
//! `"<br/>\n"`). This one rule reproduces the exact blank-line spacing of both
//! the no-lemma and multi-lemma captures.
//!
//! ## Element order
//! 1. `theory NAME begin` header line
//! 2. one blank + link line per theory item, in order: Message theory, rules,
//!    Tactic(s), Raw sources, Refined sources
//! 3. one blank + the `add lemma` link for position `<first>`
//! 4. for each lemma: one blank, the lemma's body lines, one blank, the lemma's
//!    trailing `add lemma` link (targeting that lemma's name)
//! 5. one blank + `end`
//!
//! When there are zero lemmas, step 4 contributes nothing, which leaves TWO
//! blank lines between the `<first>` add-link and `end` (matching the capture).
//!
//! ## Slots that come from the prover (opaque here)
//! The lemma declaration HTML (`decl_html`: the pretty-printed `lemma NAME:` +
//! quantifier + formula, already entity-escaped and wrapped in `hl_operator`
//! spans), the rules label/count, the sources descriptions, and — for a solved
//! proof — each proof step's method HTML and case names. Everything else (the
//! anchors, keywords, indentation, links) is generated here.
//!
//! ## Indices
//! Every internal href uses the resolved numeric theory index, never `#`.

/// A theory item shown as a top link in the proof-script pane.
pub enum Item<'a> {
    /// `Message theory` link.
    Message,
    /// Multiset rewriting rules link. `label` is the prover's wording
    /// (`"Multiset rewriting rules"`, or with `" and restrictions"`), `count`
    /// the rule count.
    Rules { label: &'a str, count: usize },
    /// `Tactic(s)` link.
    Tactic,
    /// `Raw sources` link; `desc` e.g. `"4 cases, deconstructions complete"`.
    RawSources { desc: &'a str },
    /// `Refined sources` link; note the label carries a trailing space.
    RefinedSources { desc: &'a str },
}

/// How a lemma's proof is displayed.
pub enum Proof<'a> {
    /// Unproven: a single `by sorry` proof-step line. The declaration and the
    /// edit/delete line are emitted bare (no status wrapper).
    Sorry,
    /// A solved/partial proof rendered as an explicit list of proof lines.
    ///
    /// Observed: when a lemma carries a proof, the whole lemma header — the
    /// declaration HTML plus the following edit/delete line — is wrapped in a
    /// single `<span class="{status}">…</span>` reflecting the lemma's overall
    /// proof status (`hl_good` for the proved lemmas in the corpus). The wrapper
    /// opens immediately before the declaration and closes right after the
    /// delete-lemma anchor (spanning the intervening `<br/>` line breaks).
    Steps {
        /// Lemma-level status class carried by the header wrapper span.
        status: &'a str,
        /// The rendered proof-tree lines, in document order.
        lines: Vec<ProofLine<'a>>,
    },
}

/// One line of a rendered proof tree.
pub enum ProofLine<'a> {
    /// A proof-method step (an applied method or a leaf such as `SOLVED`).
    Step {
        depth: usize,
        /// Status class, e.g. `"hl_good"`.
        status: &'a str,
        /// Full href, e.g. `/thy/trace/3/main/proof/exec/_/B_2`.
        href: String,
        /// Prover method HTML, e.g. `<span class="hl_keyword">simplify</span>`.
        method_html: &'a str,
        /// Annotation shown in the remove-step anchor (usually empty).
        annotation: &'a str,
        /// Whether the line is prefixed with a wrapped `by ` keyword.
        by: bool,
    },
    /// A `case NAME` header.
    Case {
        depth: usize,
        status: &'a str,
        name: &'a str,
    },
    /// A `next` separator between sibling cases.
    Next { depth: usize, status: &'a str },
    /// A `qed` closing a case block.
    Qed { depth: usize, status: &'a str },
}

/// A single lemma block.
pub struct Lemma<'a> {
    /// Lemma name (used in the edit/delete/add/proof links).
    pub name: &'a str,
    /// Opaque prover-produced declaration HTML (`lemma NAME:` + formula).
    pub decl_html: &'a str,
    /// Proof display.
    pub proof: Proof<'a>,
}

/// The whole proof-script pane input.
pub struct Overview<'a> {
    pub theory_name: &'a str,
    pub index: u64,
    pub items: Vec<Item<'a>>,
    pub lemmas: Vec<Lemma<'a>>,
}

fn indent(depth: usize) -> String {
    "&nbsp;&nbsp;".repeat(depth)
}

/// Render one proof-tree line (public so the line grammar can be unit-tested).
pub fn render_proof_line(line: &ProofLine) -> String {
    match line {
        ProofLine::Step {
            depth,
            status,
            href,
            method_html,
            annotation,
            by,
        } => {
            let ind = indent(*depth);
            let by_prefix = if *by {
                format!(r#"<span class="{status}"><span class="hl_keyword">by</span> </span>"#)
            } else {
                String::new()
            };
            format!(
                r#"{ind}{by_prefix}<a class="internal-link proof-step {status}" href="{href}">{method_html}</a><a class="internal-link remove-step" href="{href}">{annotation}</a>"#
            )
        }
        ProofLine::Case {
            depth,
            status,
            name,
        } => format!(
            r#"{}<span class="{status}"><span class="hl_keyword">case</span> {name}</span>"#,
            indent(*depth)
        ),
        ProofLine::Next { depth, status } => format!(
            r#"{}<span class="{status}"><span class="hl_keyword">next</span></span>"#,
            indent(*depth)
        ),
        ProofLine::Qed { depth, status } => format!(
            r#"{}<span class="{status}"><span class="hl_keyword">qed</span></span>"#,
            indent(*depth)
        ),
    }
}

fn item_line(item: &Item, idx: u64) -> String {
    match item {
        Item::Message => format!(
            r#"<a class="internal-link" href="/thy/trace/{idx}/main/message"><strong>Message theory</strong> </a>"#
        ),
        Item::Rules { label, count } => format!(
            r#"<a class="internal-link" href="/thy/trace/{idx}/main/rules"><strong>{label}</strong> ({count})</a>"#
        ),
        Item::Tactic => format!(
            r#"<a class="internal-link" href="/thy/trace/{idx}/main/tactic"><strong>Tactic(s)</strong> </a>"#
        ),
        Item::RawSources { desc } => format!(
            r#"<a class="internal-link" href="/thy/trace/{idx}/main/cases/raw/0/0"><strong>Raw sources</strong> ({desc})</a>"#
        ),
        Item::RefinedSources { desc } => format!(
            r#"<a class="internal-link" href="/thy/trace/{idx}/main/cases/refined/0/0"><strong>Refined sources </strong> ({desc})</a>"#
        ),
    }
}

fn add_link(idx: u64, target: &str) -> String {
    format!(r#"<a class="internal-link add" href="/thy/trace/{idx}/main/add/{target}">add lemma</a>"#)
}

fn edit_delete_line(idx: u64, name: &str) -> String {
    format!(
        r#"<a class="internal-link edit" href="/thy/trace/{idx}/main/edit/{name}">edit lemma</a>  or  <a class="internal-link delete" href="/thy/trace/{idx}/main/delete/{name}">delete lemma</a>"#
    )
}

fn sorry_line(idx: u64, name: &str) -> String {
    format!(
        r#"<span class="hl_keyword">by</span> <a class="internal-link proof-step sorry-step" href="/thy/trace/{idx}/main/proof/{name}"><span class="hl_keyword">sorry</span></a>"#
    )
}

/// The theory header line: `theory NAME begin`.
fn header_line(name: &str, idx: u64) -> String {
    format!(
        r#"<span class="hl_keyword">theory</span> <a class="internal-link help" href="/thy/trace/{idx}/main/help">{name}</a> <span class="hl_keyword">begin</span>"#
    )
}

/// Render the full inner HTML of the `#proof` west pane.
pub fn render_proof_script(o: &Overview) -> String {
    let idx = o.index;
    // Build the flat element list.
    let mut elems: Vec<String> = Vec::new();
    elems.push(header_line(o.theory_name, idx));
    for item in &o.items {
        elems.push(String::new());
        elems.push(item_line(item, idx));
    }
    elems.push(String::new());
    elems.push(add_link(idx, "%3Cfirst%3E"));
    if o.lemmas.is_empty() {
        elems.push(String::new());
        elems.push(String::new());
    } else {
        for lemma in &o.lemmas {
            elems.push(String::new());
            match &lemma.proof {
                Proof::Sorry => {
                    // Bare declaration, edit/delete line, then a single `by sorry`.
                    elems.push(lemma.decl_html.to_string());
                    elems.push(edit_delete_line(idx, lemma.name));
                    elems.push(sorry_line(idx, lemma.name));
                }
                Proof::Steps { status, lines } => {
                    // The header (declaration + edit/delete line) is wrapped in a
                    // status span that opens before the declaration and closes
                    // after the delete anchor; the proof lines follow unwrapped.
                    elems.push(format!(r#"<span class="{status}">{}"#, lemma.decl_html));
                    elems.push(format!("{}</span>", edit_delete_line(idx, lemma.name)));
                    for l in lines {
                        elems.push(render_proof_line(l));
                    }
                }
            }
            elems.push(String::new());
            elems.push(add_link(idx, lemma.name));
        }
        elems.push(String::new());
    }
    elems.push(header_end());

    let mut out = String::new();
    for e in &elems {
        out.push_str(e);
        out.push_str("<br/>\n");
    }
    out.push(' ');
    out
}

fn header_end() -> String {
    r#"<span class="hl_keyword">end</span>"#.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proof_step_simplify_line() {
        let l = ProofLine::Step {
            depth: 0,
            status: "hl_good",
            href: "/thy/trace/3/main/proof/exec".to_string(),
            method_html: r#"<span class="hl_keyword">simplify</span>"#,
            annotation: "",
            by: false,
        };
        assert_eq!(
            render_proof_line(&l),
            r#"<a class="internal-link proof-step hl_good" href="/thy/trace/3/main/proof/exec"><span class="hl_keyword">simplify</span></a><a class="internal-link remove-step" href="/thy/trace/3/main/proof/exec"></a>"#
        );
    }

    #[test]
    fn case_header_indented() {
        let l = ProofLine::Case {
            depth: 1,
            status: "hl_good",
            name: "B_2",
        };
        assert_eq!(
            render_proof_line(&l),
            r#"&nbsp;&nbsp;<span class="hl_good"><span class="hl_keyword">case</span> B_2</span>"#
        );
    }

    #[test]
    fn by_step_contradiction() {
        let l = ProofLine::Step {
            depth: 4,
            status: "hl_good",
            href: "/thy/trace/3/main/proof/unforgeability/_/B_2/S_1/B_1/case_1/B_2".to_string(),
            method_html: r#"<span class="hl_keyword">contradiction</span> <span class="hl_comment">/* cyclic */</span>"#,
            annotation: "",
            by: true,
        };
        let expected = r#"&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="hl_good"><span class="hl_keyword">by</span> </span><a class="internal-link proof-step hl_good" href="/thy/trace/3/main/proof/unforgeability/_/B_2/S_1/B_1/case_1/B_2"><span class="hl_keyword">contradiction</span> <span class="hl_comment">/* cyclic */</span></a><a class="internal-link remove-step" href="/thy/trace/3/main/proof/unforgeability/_/B_2/S_1/B_1/case_1/B_2"></a>"#;
        assert_eq!(render_proof_line(&l), expected);
    }

    #[test]
    fn qed_and_next() {
        assert_eq!(
            render_proof_line(&ProofLine::Qed { depth: 1, status: "hl_good" }),
            r#"&nbsp;&nbsp;<span class="hl_good"><span class="hl_keyword">qed</span></span>"#
        );
        assert_eq!(
            render_proof_line(&ProofLine::Next { depth: 3, status: "hl_good" }),
            r#"&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="hl_good"><span class="hl_keyword">next</span></span>"#
        );
    }
}
