//! Term / fact pretty-printer reproducing the oracle's rendering.
//!
//! Every rule here traces to an oracle observation (see workspace/BEHAVIOR.md
//! and the probes t_terms, t_xor, t_nat, f_nullary).

use crate::ast::*;

/// Render a variable: sort prefix + base name + optional ".idx" (idx > 0).
pub fn pp_var(v: &VarSpec) -> String {
    let prefix = match v.sort {
        SortHint::Fresh => "~",
        SortHint::Pub => "$",
        SortHint::Nat => "%",
        SortHint::Node => "#",
        SortHint::Msg | SortHint::Untagged => "",
        // Suffix-sorted variables carry an explicit ":sort"; best-effort.
        SortHint::Suffix(_) => "",
    };
    if v.idx > 0 {
        format!("{}{}.{}", prefix, v.name, v.idx)
    } else {
        format!("{}{}", prefix, v.name)
    }
}

/// Flatten a right-nested pair term into its element list.
fn flatten_pair(t: &Term, out: &mut Vec<String>) {
    match t {
        Term::Pair(items) => {
            for it in items {
                flatten_pair(it, out);
            }
        }
        Term::App(name, args) if name == "pair" && args.len() == 2 => {
            flatten_pair(&args[0], out);
            flatten_pair(&args[1], out);
        }
        other => out.push(pp_term(other)),
    }
}

/// Collect the operands of a left/right-nested chain of the same binary op.
fn flatten_binop(op: BinOp, t: &Term, out: &mut Vec<Term>) {
    if let Term::BinOp(o, a, b) = t {
        if *o == op {
            flatten_binop(op, a, out);
            flatten_binop(op, b, out);
            return;
        }
    }
    out.push(t.clone());
}

fn pp_binop(op: BinOp, a: &Term, b: &Term) -> String {
    match op {
        // Exponentiation is shown infix without surrounding parentheses.
        BinOp::Exp => format!("{}^{}", pp_term(a), pp_term(b)),
        // The AC operators are parenthesised and joined by their symbol.
        BinOp::Mult | BinOp::Union | BinOp::Xor | BinOp::NatPlus => {
            let sym = match op {
                BinOp::Mult => "*",
                BinOp::Union => "++",
                BinOp::Xor => "\u{2295}", // (+)
                BinOp::NatPlus => "%+",
                BinOp::Exp => unreachable!(),
            };
            let whole = Term::BinOp(op, Box::new(a.clone()), Box::new(b.clone()));
            let mut operands = Vec::new();
            flatten_binop(op, &whole, &mut operands);
            let mut parts: Vec<String> = operands.iter().map(pp_term).collect();
            // XOR arguments are normalised (sorted); observed in probe t_xor.
            if op == BinOp::Xor {
                parts.sort();
            }
            format!("({})", parts.join(sym))
        }
    }
}

/// Render a term the way the oracle prints it inside facts.
pub fn pp_term(t: &Term) -> String {
    match t {
        Term::Var(v) => pp_var(v),
        Term::PubLit(s) => format!("'{}'", s),
        Term::FreshLit(s) => format!("~'{}'", s),
        Term::NatLit(s) => format!("%'{}'", s),
        Term::Number(n) => n.to_string(),
        Term::NumberOne => "1".to_string(),
        Term::NatOne => "%1".to_string(),
        Term::DhNeutral => "DH_neutral".to_string(),
        Term::App(name, args) => {
            if name == "pair" && args.len() == 2 {
                let mut elems = Vec::new();
                flatten_pair(t, &mut elems);
                format!("<{}>", elems.join(", "))
            } else if args.is_empty() {
                name.clone()
            } else {
                let parts: Vec<String> = args.iter().map(pp_term).collect();
                format!("{}({})", name, parts.join(", "))
            }
        }
        Term::AlgApp(name, a, b) => format!("{}({}, {})", name, pp_term(a), pp_term(b)),
        Term::Pair(_) => {
            let mut elems = Vec::new();
            flatten_pair(t, &mut elems);
            format!("<{}>", elems.join(", "))
        }
        Term::Diff(a, b) => format!("diff({}, {})", pp_term(a), pp_term(b)),
        Term::BinOp(op, a, b) => pp_binop(*op, a, b),
        Term::PatMatch(inner) => format!("={}", pp_term(inner)),
    }
}

/// Render a fact: optional `!` for persistent, then `Name( args )`.
/// Empty argument list renders as `Name( )`.
pub fn pp_fact(f: &Fact) -> String {
    let bang = if f.persistent { "!" } else { "" };
    if f.args.is_empty() {
        format!("{}{}( )", bang, f.name)
    } else {
        let parts: Vec<String> = f.args.iter().map(pp_term).collect();
        format!("{}{}( {} )", bang, f.name, parts.join(", "))
    }
}

/// Render a bracketed fact list as it appears inside a rule: `[ f1, f2 ]`, or
/// `[ ]` when empty.
pub fn pp_fact_list(fs: &[Fact]) -> String {
    if fs.is_empty() {
        "[ ]".to_string()
    } else {
        let parts: Vec<String> = fs.iter().map(pp_fact).collect();
        format!("[ {} ]", parts.join(", "))
    }
}

/// Render a rule the way the oracle prints it (single-line body; the oracle
/// wraps very long rules across several lines - see BEHAVIOR.md gaps):
///
/// ```text
/// rule (modulo E) Name:
///    [ prems ] --> [ concls ]
/// ```
///
/// with `--[ acts ]->` in place of `-->` when the rule has action facts.
pub fn pp_rule(r: &Rule) -> String {
    let modulo = r.modulo.as_deref().unwrap_or("E");
    let prems = pp_fact_list(&r.premises);
    let concls = pp_fact_list(&r.conclusions);
    let arrow = if r.actions.is_empty() {
        "-->".to_string()
    } else {
        let acts: Vec<String> = r.actions.iter().map(pp_fact).collect();
        format!("--[ {} ]->", acts.join(", "))
    };
    format!("rule (modulo {}) {}:\n   {} {} {}", modulo, r.name, prems, arrow, concls)
}
