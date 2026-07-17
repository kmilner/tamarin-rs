//! Route model for the interactive web UI.
//!
//! Every observed request path has the shape
//! `/thy/<theory-kind>/<index>/<handler>/<args…>` where:
//! * `<theory-kind>` is the analysis kind — only `trace` appears in the corpus
//!   (a `diff` kind is plausible but unobserved).
//! * `<index>` is either `#` (the "current" theory version) or a decimal number.
//! * `<handler>` selects the response family. Observed handlers and their
//!   response `kind`:
//!     - `main/…`                    -> JSON envelope (`{html,title}` / `{redirect}`)
//!     - `overview/…`                -> full-page HTML
//!     - `intdot/…`                  -> HTML mini-page
//!     - `interactive-graph-def/…`   -> DOT
//!     - `next/…`, `prev/…`          -> text (a navigation URL)
//!     - `autoprove/…`               -> JSON (`{redirect}`), or text on timeout
//!     - `source`, `message`         -> text (theory source)
//!
//! Under `main`, the sub-handlers are: `help`, `message`, `rules`, `tactic`,
//! `cases/{raw|refined}/{level}/{n}`, `lemma/{name}`, `add/{pos}`,
//! `edit/{name}`, `delete/{name}`, `method/{lemma}/{n}`, and
//! `proof/{lemma}/{path…}` (the proof path is a sequence of case-name segments,
//! the root being `_`).
//!
//! This module parses a path into a structured value; it is descriptive (the
//! route grammar as observed), not a dispatcher.

/// Theory version selector.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Index {
    /// `#` — the server's "current" theory version.
    Current,
    /// An explicit decimal version index.
    Num(u64),
}

impl Index {
    fn parse(s: &str) -> Option<Index> {
        if s == "#" {
            Some(Index::Current)
        } else {
            s.parse::<u64>().ok().map(Index::Num)
        }
    }
}

/// A `main/*` sub-handler.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Main {
    Help,
    Message,
    Rules,
    Tactic,
    Cases { refined: bool, level: usize, n: usize },
    Lemma(String),
    Add(String),
    Edit(String),
    Delete(String),
    Method { lemma: String, n: usize },
    Proof { lemma: String, path: Vec<String> },
    /// Any unrecognized `main/*` tail.
    Other(Vec<String>),
}

/// The selected handler and its arguments.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Handler {
    Source,
    Message,
    Main(Main),
    Overview(Vec<String>),
    Intdot(Vec<String>),
    InteractiveGraphDef(Vec<String>),
    Next(Vec<String>),
    Prev(Vec<String>),
    Autoprove(Vec<String>),
    /// Unrecognized handler with its raw tail.
    Other { name: String, tail: Vec<String> },
}

/// A parsed route.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Route {
    pub theory_kind: String,
    pub index: Index,
    pub handler: Handler,
}

fn owned(v: &[&str]) -> Vec<String> {
    v.iter().map(|s| s.to_string()).collect()
}

fn parse_main(tail: &[&str]) -> Main {
    match tail {
        ["help"] => Main::Help,
        ["message"] => Main::Message,
        ["rules"] => Main::Rules,
        ["tactic"] => Main::Tactic,
        ["cases", kind, level, n]
            if (*kind == "raw" || *kind == "refined")
                && level.parse::<usize>().is_ok()
                && n.parse::<usize>().is_ok() =>
        {
            Main::Cases {
                refined: *kind == "refined",
                level: level.parse().unwrap(),
                n: n.parse().unwrap(),
            }
        }
        ["lemma", name] => Main::Lemma((*name).to_string()),
        ["add", pos] => Main::Add((*pos).to_string()),
        ["edit", name] => Main::Edit((*name).to_string()),
        ["delete", name] => Main::Delete((*name).to_string()),
        ["method", lemma, n] if n.parse::<usize>().is_ok() => Main::Method {
            lemma: (*lemma).to_string(),
            n: n.parse().unwrap(),
        },
        [proof, lemma, rest @ ..] if *proof == "proof" => Main::Proof {
            lemma: (*lemma).to_string(),
            path: owned(rest),
        },
        _ => Main::Other(owned(tail)),
    }
}

impl Route {
    /// Parse a request path such as `/thy/trace/#/main/proof/exec/_/B_2`.
    /// Returns `None` if the path is not under `/thy/<kind>/<index>/…`.
    pub fn parse(path: &str) -> Option<Route> {
        let trimmed = path.strip_prefix('/').unwrap_or(path);
        let segs: Vec<&str> = trimmed.split('/').collect();
        // Need at least: thy / kind / index / handler
        if segs.len() < 4 || segs[0] != "thy" {
            return None;
        }
        let theory_kind = segs[1].to_string();
        let index = Index::parse(segs[2])?;
        let handler_name = segs[3];
        let tail = &segs[4..];
        let handler = match handler_name {
            "source" => Handler::Source,
            "message" => Handler::Message,
            "main" => Handler::Main(parse_main(tail)),
            "overview" => Handler::Overview(owned(tail)),
            "intdot" => Handler::Intdot(owned(tail)),
            "interactive-graph-def" => Handler::InteractiveGraphDef(owned(tail)),
            "next" => Handler::Next(owned(tail)),
            "prev" => Handler::Prev(owned(tail)),
            "autoprove" => Handler::Autoprove(owned(tail)),
            other => Handler::Other {
                name: other.to_string(),
                tail: owned(tail),
            },
        };
        Some(Route {
            theory_kind,
            index,
            handler,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_main_rules() {
        let r = Route::parse("/thy/trace/#/main/rules").unwrap();
        assert_eq!(r.theory_kind, "trace");
        assert_eq!(r.index, Index::Current);
        assert_eq!(r.handler, Handler::Main(Main::Rules));
    }

    #[test]
    fn parses_cases_with_numbers() {
        let r = Route::parse("/thy/trace/1/main/cases/refined/0/2").unwrap();
        assert_eq!(r.index, Index::Num(1));
        assert_eq!(
            r.handler,
            Handler::Main(Main::Cases { refined: true, level: 0, n: 2 })
        );
    }

    #[test]
    fn parses_proof_path() {
        let r = Route::parse("/thy/trace/3/main/proof/exec/_/B_2").unwrap();
        assert_eq!(
            r.handler,
            Handler::Main(Main::Proof {
                lemma: "exec".to_string(),
                path: vec!["_".to_string(), "B_2".to_string()],
            })
        );
    }

    #[test]
    fn parses_method_and_dot_and_text() {
        assert_eq!(
            Route::parse("/thy/trace/#/main/method/exec/1").unwrap().handler,
            Handler::Main(Main::Method { lemma: "exec".to_string(), n: 1 })
        );
        assert!(matches!(
            Route::parse("/thy/trace/#/interactive-graph-def/proof/exec").unwrap().handler,
            Handler::InteractiveGraphDef(_)
        ));
        assert_eq!(
            Route::parse("/thy/trace/#/source").unwrap().handler,
            Handler::Source
        );
    }

    #[test]
    fn rejects_non_thy() {
        assert!(Route::parse("/static/css/x.css").is_none());
        assert!(Route::parse("/").is_none());
    }
}
