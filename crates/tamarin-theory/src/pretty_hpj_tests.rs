// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;

#[test]
fn text_renders_verbatim() {
    assert_eq!(Doc::text("hello").render(), "hello");
    assert_eq!(Doc::empty().render(), "");
}

#[test]
fn beside_concats() {
    assert_eq!(Doc::text("a").beside(Doc::text("b")).render(), "ab");
}

#[test]
fn beside_sp_inserts_space() {
    assert_eq!(Doc::text("a").beside_sp(Doc::text("b")).render(), "a b");
}

#[test]
fn text_hs_keeps_the_empty_run() {
    // HS `text "" <+> text "b"` = " b" and `d <+> text ""` = "a ";
    // `Doc::text("")` collapses to `Empty`, which loses both spaces.
    assert_eq!(Doc::text("a").beside_sp(Doc::text_hs("")).render(), "a ");
    assert_eq!(Doc::text_hs("").beside_sp(Doc::text("b")).render(), " b");
    assert_eq!(Doc::text("a").beside_sp(Doc::text("")).render(), "a");
    // Non-empty runs are `Doc::text`.
    assert_eq!(Doc::text("a").beside_sp(Doc::text_hs("b")).render(), "a b");
}

#[test]
fn above_inserts_newline() {
    let d = Doc::text("a").above(Doc::text("b"));
    assert_eq!(d.render(), "a\nb");
}

#[test]
fn nest_indents_continuation() {
    // HS `$$` (above_g=false) ALLOWS the second line's first text
    // to overlap onto p's last line when nest gap permits.
    // `text "a" $$ nest 2 (text "b")` becomes "a b" (overlap with
    // 1 inline space, since `a` took col 0 and `nest 2` shifts to
    // col 2 = 1 space after `a`).  HS `nilAboveNest g=False k=1 q`
    // line: `textBeside_ (Str " ") q`.
    let d = Doc::text("a").above(Doc::text("b").nest(2));
    assert_eq!(d.render(), "a b");
    // Forcing a newline requires `$+$` (above_g=true) or `sep` of
    // multi-line content.
    let d = sep(vec![Doc::text("aaaaaa"), Doc::text("bbbbbb")]);
    let out = d.render_with(5, 5);
    assert!(out.contains('\n'), "got: {out}");
}

#[test]
fn sep_fits_horizontal() {
    let d = sep(vec![Doc::text("a"), Doc::text("b"), Doc::text("c")]);
    assert_eq!(d.render(), "a b c");
}

#[test]
fn sep_breaks_when_too_wide() {
    // Force the sep to wrap by exceeding ribbon width.
    let long = "x".repeat(40);
    let d = sep(vec![Doc::text(&long), Doc::text(&long)]).nest(0);
    let out = d.render_with(50, 50);
    assert!(out.contains('\n'), "expected wrap: {out}");
}

#[test]
fn fsep_packs_greedy() {
    let words: Vec<Doc> = (0..10).map(|i| Doc::text(format!("w{}", i))).collect();
    let d = fsep(words);
    let out = d.render_with(20, 20);
    assert!(out.contains('\n'));
    // First line should hold several words.
    let first_line = out.split('\n').next().unwrap();
    assert!(first_line.starts_with("w0 w1"), "got: {out}");
}

#[test]
fn nicest1_w_shrinks_at_nilabove() {
    // Verify that w shrinks at NilAbove: a sep where the LEFT fits
    // but the right would need a shrunk budget to choose vertical.
    //
    // sep [aaa, sep [bbb, ccc]] at width 6: outer sep tries flat
    // "aaa bbb ccc" (11 chars) — doesn't fit width 6, wraps.
    // Result: "aaa\nbbb ccc" or "aaa\nbbb\nccc"?
    // Per HS algorithm, after the outer NilAbove, inner sep gets
    // w = 6 - 0 = 6 (sl=0 since text started at start-of-line).
    // Inner flat "bbb ccc" = 7 chars > 6, so wraps to "bbb\nccc".
    let d = sep(vec![
        Doc::text("aaa"),
        sep(vec![Doc::text("bbb"), Doc::text("ccc")]),
    ]);
    let out = d.render_with(6, 6);
    assert_eq!(out, "aaa\nbbb\nccc", "got: {out:?}");
}

#[test]
fn punctuate_separates() {
    let docs = vec![Doc::text("a"), Doc::text("b"), Doc::text("c")];
    let p = punctuate(Doc::text(","), docs);
    let d = hcat(p);
    assert_eq!(d.render(), "a,b,c");
}

#[test]
fn nested_binop_w_shrinks_with_depth() {
    // Mirror the wireguard "5-deep And" case: a deep `(A ∧ B)` sep where each
    // level is `sep [opParens(left) <+> "∧", opParens(right)]`.
    //
    // With the ribbon measured from the line start (sl=0 on the first line),
    // once the outermost sep wraps to vertical the inner sep sees `w` shrunk
    // by `sl` (the column where the prior text started) and must wrap too.
    let conn = |l: Doc, r: Doc| sep(vec![l.beside_sp(Doc::text("\u{2227}")), r]);
    // 36-char leaf, three bracket/operator levels on top: cannot fit at 50.
    let mut d = Doc::text("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"); // 36 chars
    for _ in 0..3 {
        d = conn(
            Doc::text("[").beside(d).beside(Doc::text("]")),
            Doc::text("y"),
        );
    }
    let out = d.render_with(50, 50);
    // Verify SOMETHING wrapped (we'd be at >50 cols otherwise).
    assert!(out.contains('\n'));
}

#[test]
fn wireguard_5_deep_and_layout() {
    // Mirror wireguard UKS_resistance lemma's deep And exactly.
    // Goal: produce HS's wrap shape (break at the inner And) for:
    //   (((((pki1 = pki2) ∧ (pkr1 = pkr2)) ∧ (peki1 = peki2)) ∧
    //     (pekr1 = pekr2)) ∧
    //    (psk1 = psk2))
    // The top-level Doc has 4 chars of leading indent (from
    // lemma-body), then opParens cascading.
    let op_parens = |d: Doc| Doc::text("(").beside(d).beside(Doc::text(")"));
    let eq = |a: &str, b: &str| Doc::text(format!("{} = {}", a, b));
    let and = "\u{2227}";
    let conn = |l: Doc, r: Doc| {
        // HS: sep [opParens(l) <+> op, opParens(r)]
        sep(vec![op_parens(l).beside_sp(Doc::text(and)), op_parens(r)])
    };
    let a = eq("pki1", "pki2");
    let b = eq("pkr1", "pkr2");
    let c = eq("peki1", "peki2");
    let d_eq = eq("pekr1", "pekr2");
    let e = eq("psk1", "psk2");
    // ((((A ∧ B) ∧ C) ∧ D) ∧ E)
    let ab = conn(a, b);
    let abc = conn(ab, c);
    let abcd = conn(abc, d_eq);
    let abcde = conn(abcd, e);
    // Wrap in outer opParens (from Implies's right opParens).
    let full = op_parens(abcde);
    // Lay out at 4-space indent.
    let indented = Doc::text("    ").beside(full);
    let out = indented.render();
    // HS produces (we want):
    //     (((((pki1 = pki2) ∧ (pkr1 = pkr2)) ∧ (peki1 = peki2)) ∧
    //       (pekr1 = pekr2)) ∧
    //      (psk1 = psk2))
    let expected =
            "    (((((pki1 = pki2) \u{2227} (pkr1 = pkr2)) \u{2227} (peki1 = peki2)) \u{2227}\n      (pekr1 = pekr2)) \u{2227}\n     (psk1 = psk2))";
    assert_eq!(out, expected, "got:\n{out}\n---\nexpected:\n{expected}");
}

#[test]
fn wireguard_aead_fsep_breaks_before_e() {
    // Mirror wireguard Handshake_Complete In( ... ) input.
    // Goal: pp_term `aead( h(<pair>), 'e', h(<pair>) )` at indent
    // = 10 should break before `'e',` per HS (line 626 in HS
    // output).
    //
    // HS's `prettyTerm` for App uses
    //   `ppFun f ts = text (f++"(") <> fsep (punctuate "," (map ppTerm ts)) <> text ")"`.
    // The `fsep` breaks at item boundaries when the next item
    // wouldn't fit.
    //
    // We approximate the inner h(<pair>) as a long opaque text
    // and verify the fsep breaks before "'e',".
    let arg1 = Doc::text("h(<h(<h(<h(<ci2, pekR, '1'>), z, '1'>), z.1, '1'>), ~psk, '3'>)");
    let arg2 = Doc::text("'e'");
    let arg3 = Doc::text(
        "h(<h(<hi1, pekR>), h(<h(<h(<h(<ci2, pekR, '1'>), z, '1'>), z.1, '1'>), ~psk, '2'>)>)",
    );
    let comma = Doc::text(",");
    let items = punctuate(comma, vec![arg1, arg2, arg3]);
    let body = fsep(items);
    let full = Doc::text("aead(").beside(body).beside(Doc::text(")"));
    // Layout at col 10 (after leading "          ").
    let lead = Doc::text("          ");
    let d = lead.beside(full);
    let out = d.render();
    // Verify there's a break before "'e',".
    let lines: Vec<&str> = out.split('\n').collect();
    assert!(lines.len() >= 3, "expected at least 3 lines, got: {out}");
    // Find the line that starts with the 'e' (after leading whitespace).
    let has_e_alone = lines.iter().any(|l| l.trim_start().starts_with("'e'"));
    assert!(has_e_alone, "expected 'e' on its own line; got:\n{out}");
}

#[test]
fn sep_vertical_col_alignment() {
    // sep [text "a", text "b"] when wrapped: should b appear at
    // col 0 (where a started) or somewhere else?
    let d = sep(vec![Doc::text("aaaaaaaaaa"), Doc::text("bbbbbbbbbb")]);
    let out = d.render_with(10, 10);
    // Expected: "aaaaaaaaaa\nbbbbbbbbbb" — b at col 0.
    assert_eq!(out, "aaaaaaaaaa\nbbbbbbbbbb", "got: {out:?}");
}

#[test]
fn nested_sep_indent_alignment() {
    // sep [quant, sep [dante.nest(1), conn, dsucc.nest(1)]]
    // When outer wraps, where does inner sep start?
    // If inner sep also wraps, where do conn and dsucc go?
    let quant = Doc::text("Q.");
    let dante = Doc::text("DANTE");
    let conn = Doc::text("c");
    let dsucc = Doc::text("DSUCC");
    let inner = sep(vec![dante.nest(1), conn, dsucc.nest(1)]);
    let outer = sep(vec![quant, inner]);
    // At width 10, both seps wrap.
    let out = outer.render_with(10, 10);
    // We want HS-like alignment:
    // "Q.\n DANTE\nc\n DSUCC"
    assert_eq!(out, "Q.\n DANTE\nc\n DSUCC");
}

// The guarded-formula layout runs through `guarded_to_doc` on this
// engine — see `pretty_formula.rs::pretty_guarded_doublequoted`.

#[test]
fn pkcs11_eleven_tuple_close_bracket_glue() {
    // Regression for the pkcs11-templates variant-subst tuple wrap
    // (cannot_obtain_key et al.).  HS renders the AC-variant block via
    //   numbered' (map ppConj substs)   (SubstVFresh.hs:223-227)
    // where each numbered item is `text i <> ". " <> vcat[prettyEq..]`
    // at nest 4.  The `". " <>` BESIDE onto the multi-line vcat measures
    // the inner fcat's ribbon from the OUTER (numbered) line start, so an
    // 11-tuple `<x.16, …, x.26>` breaks BEFORE x.26 (gluing `>`).
    // Confirms the engine reproduces the HS structure
    // byte-for-byte (verified against Text.PrettyPrint.HughesPJ ll=110).
    // term_doc = pair_doc(11 elements) = fcat([ "<", e0", ", ... e10, ">" ]).
    // Elements x.16..x.26 are 4 chars each, nest(1)'d, comma-suffixed.
    let mk_pair = || {
        let n = 11;
        let mut parts: Vec<Doc> = Vec::with_capacity(n + 2);
        parts.push(Doc::text("<"));
        for i in 0..n {
            let name = format!("x.{}", 16 + i);
            let mut d = Doc::text(name);
            if i + 1 < n {
                d = d.beside(Doc::text(", "));
            }
            parts.push(d.nest(1));
        }
        parts.push(Doc::text(">"));
        fcat(parts)
    };
    // HS structure (SubstVFresh.hs:227-229 + Class.hs:252-264):
    //   numbered' = numbered (text "") . map (text ". " <>)
    //   each item = text(flushRight w i) <> (text ". " <> vcat[prettyEq..])
    //   prettyEq (a,b) = text a $$ nest 6 (text "=" <-> term)
    // The whole `variants (modulo AC)` block sits at nest 4.
    let prettyeq = |v: &str, t: Doc| Doc::text(v).above(Doc::text("=").beside_sp(t).nest(6));
    let conj = prettyeq("v", mk_pair());
    let item = Doc::text("3").beside(Doc::text(". ").beside(conj));
    let out = item.nest(4).render();
    // HS-faithful expectation: break BEFORE x.26, glue '>' to it.
    let expected = "    3. v     = <x.16, x.17, x.18, x.19, x.20, x.21, x.22, x.23, x.24, x.25, \n                x.26>";
    assert_eq!(out, expected, "got:\n{out}");
}

#[test]
fn dnp3_tuple_fill_keystatus_on_first_line() {
    // dnp3-proven Action goal:
    //   solve( !KU( senc(<~CDSK_j_USR_O, MDSK_j_USR_O, KSQ.1, $USR,
    //                     keystatus, CD_j>, ~UK_i_USR_O) ) @ #vk.11 )
    // HS packs `keystatus,` on the FIRST line of the tuple `fcat`
    // (the element fits within the ribbon measured from the line
    // start).  This pins the `fcat` fill-boundary byte-for-byte vs
    // `Text.PrettyPrint.HughesPJ` at lineLength 110 / ribbon 73.
    let elems = [
        "~CDSK_j_USR_O",
        "MDSK_j_USR_O",
        "KSQ.1",
        "$USR",
        "keystatus",
        "CD_j",
    ];
    let n = elems.len();
    let mut parts: Vec<Doc> = Vec::new();
    parts.push(Doc::text("<"));
    for (i, e) in elems.iter().enumerate() {
        let mut d = Doc::text(*e);
        if i + 1 < n {
            d = d.beside(Doc::text(", "));
        }
        parts.push(d.nest(1));
    }
    parts.push(Doc::text(">"));
    let tuple = fcat(parts);
    // senc( tuple , ~UK_i_USR_O ): "senc(" <> fsep(punctuate(",", [tuple,key])) <> ")"
    let senc_body = fsep(punctuate(
        Doc::char(','),
        vec![tuple, Doc::text("~UK_i_USR_O")],
    ));
    let senc = Doc::text("senc(").beside(senc_body).beside(Doc::text(")"));
    // !KU( senc ): nestShort' ("!KU(", ")", fsep([senc]))
    let lead = "!KU(";
    let nku_body = fsep(punctuate(Doc::char(','), vec![senc]));
    let nn = lead.chars().count() as isize + 1;
    let above = Doc::text(lead).above(nku_body.nest(nn));
    let nku = sep(vec![above, Doc::text(")")]);
    // Action goal: solve( !KU(...) @ #vk.11 )
    let goal = nku.beside_sp(Doc::text("@")).beside_sp(Doc::text("#vk.11"));
    let solve = Doc::text("solve(")
        .beside_sp(goal)
        .beside_sp(Doc::text(")"));
    let out = solve.nest(16).render();
    let first = out.split('\n').next().unwrap();
    assert!(
        first.trim_end().ends_with("keystatus,"),
        "expected `keystatus,` on the first tuple line; got:\n{out}",
    );
}

#[test]
fn fcat_close_bracket_separate_item() {
    // A pair `<a, b, c>` modeled as an `fcat` whose closing `>` is a separate
    // final item: the closer must pack onto the last content line when it
    // fits, and only move down when it would overflow.
    let items = vec![
        Doc::text("<"),
        Doc::text("aaa,"),
        Doc::text("bbb,"),
        Doc::text("ccc,"),
        Doc::text("ddd"),
        Doc::text(">"),
    ];
    let d = fcat(items);
    // At width 12 the items pack greedily: `<aaa,bbb,` fills the first line
    // (adding `ccc,` would reach 13), and `>` still fits after `ccc,ddd`.
    let out = d.render_with(12, 12);
    assert_eq!(out, "<aaa,bbb,\nccc,ddd>");
}
