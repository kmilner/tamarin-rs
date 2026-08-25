// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Theory.Text.Pretty` (`lib/theory/src/Theory/Text/Pretty.hs`): the
//! theory-level comment and keyword combinators.  HS re-exports the highlight
//! and Doc combinators from the same module (`module Text.PrettyPrint.Highlight`,
//! `Theory/Text/Pretty.hs:10`); here they come from the Doc engine in
//! `tamarin-utils`.

pub use tamarin_utils::pretty_hpj::*;

// -- Comments (HS Theory.Text.Pretty.hs:96-112) -------------------------------

/// HS `lineComment_ s = comment $ text "//" <-> text s`
/// (`Theory/Text/Pretty.hs:96-100`).
pub fn line_comment_(s: &str) -> Doc {
    comment(Doc::text("//").beside_sp(Doc::text(s)))
}

/// HS `multiComment_ ls = comment $ fsep [text "/*", vcat (map text ls),
/// text "*/"]` (`Theory/Text/Pretty.hs:105-106`).
pub fn multi_comment_(lines: &[&str]) -> Doc {
    let body = vcat(lines.iter().map(|l| Doc::text(*l)).collect());
    comment(fsep(vec![Doc::text("/*"), body, Doc::text("*/")]))
}

/// HS `closedComment_ s = comment $ fsep [text "/*", text s, text "*/"]`
/// (`Theory/Text/Pretty.hs:111-112`).
pub fn closed_comment_(s: &str) -> Doc {
    comment(fsep(vec![Doc::text("/*"), Doc::text(s), Doc::text("*/")]))
}

// -- Keyword composites (HS Theory.Text.Pretty.hs:148-159) --------------------

/// HS `kwModulo what thy = keyword_ what <-> parens (keyword_ "modulo" <->
/// text thy)` (`Theory/Text/Pretty.hs:148-152`).
pub fn kw_modulo(what: &str, thy: &str) -> Doc {
    keyword_(what).beside_sp(parens(keyword_("modulo").beside_sp(Doc::text(thy))))
}

/// HS `kwRuleModulo = kwModulo "rule"`
/// (`Theory/Text/Pretty.hs:154-156, see line 156`).
pub fn kw_rule_modulo(thy: &str) -> Doc {
    kw_modulo("rule", thy)
}

#[cfg(test)]
mod tests {
    use super::HtmlDocGuard;
    use tamarin_utils::pretty_hpj::html_mode as engine_html_mode;

    /// The guard this module re-exports and the engine's own `html_mode()`
    /// read the same thread-local flag: this crate must not carry a second
    /// copy.
    #[test]
    fn html_mode_guard_is_shared_with_the_engine() {
        assert!(!engine_html_mode());
        {
            let _g = HtmlDocGuard::enable();
            assert!(engine_html_mode());
        }
        assert!(!engine_html_mode());
    }
}
