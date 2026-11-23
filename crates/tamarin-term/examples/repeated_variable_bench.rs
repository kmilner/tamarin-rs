//! Time one AC query with repeated variables on one backend.
//!
//! `repeated_variable_bench <maude|native> <dh|xor|mset> <unify|unifiable|variants> <query>`
//!
//! A query is a list of equations separated by `;`, the two sides of an
//! equation by `=`, and the factors of a product by `*`. A lower-case factor
//! is a message variable, an upper-case one a public name and `i:` before a
//! factor its inverse. `variants` takes the terms separated by `;` and
//! lists the variants of their tuple. The line printed is
//! `backend,sig,op,query,milliseconds,answers`. Process start, one warming
//! unification and, for `variants`, one warming variant query (which builds
//! and, on native-only, certifies the session's rule table) are outside the
//! time. Run every query in a process of its own under a timeout and a memory
//! cap: a query can run for a long time, and a second call of the same query
//! is answered from the session's memo.
#![allow(clippy::disallowed_macros)]

use std::time::Instant;

use tamarin_term::algebra_backend::AlgebraBackend;
use tamarin_term::builtin::inv;
use tamarin_term::function_symbols::AcSym;
use tamarin_term::lterm::{pub_term, LNTerm, LSort, LVar};
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::maude_sig::{dh_maude_sig, mset_maude_sig, xor_maude_sig};
use tamarin_term::rewriting::Equal;
use tamarin_term::term::{f_app_ac, f_app_list, Term};
use tamarin_term::vterm::Lit;

fn factor(text: &str) -> LNTerm {
    let text = text.trim();
    if let Some(rest) = text.strip_prefix("i:") {
        return inv(factor(rest));
    }
    if text.chars().next().is_some_and(char::is_uppercase) {
        pub_term(text.to_lowercase())
    } else {
        Term::Lit(Lit::Var(LVar::new(text, LSort::Msg, 0)))
    }
}

fn product(sym: &AcSym, text: &str) -> LNTerm {
    f_app_ac(sym.clone(), text.split('*').map(factor).collect())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    assert_eq!(
        args.len(),
        5,
        "usage: <maude|native> <dh|xor|mset> <op> <query>"
    );
    let (sig, sym) = match args[2].as_str() {
        "dh" => (dh_maude_sig(), AcSym::Mult),
        "xor" => (xor_maude_sig(), AcSym::Xor),
        "mset" => (mset_maude_sig(), AcSym::Union),
        other => panic!("unknown signature {other}"),
    };
    let handle = if args[1] == "native" {
        MaudeHandle::start_with_backend("/nonexistent", sig, AlgebraBackend::NativeOnly)
            .expect("native-only handle")
    } else {
        let path = tamarin_test_support::maude_path().unwrap_or_else(|| "maude".into());
        MaudeHandle::start(&path, sig).expect("Maude handle")
    };
    let warm = [Equal {
        lhs: product(&sym, "WA*WB"),
        rhs: product(&sym, "WB*WA"),
    }];
    handle.unify(&warm).expect("warming query");
    if args[3] == "variants" {
        // The first variant query of a session builds its rule table, and
        // native-only certifies the table (about 0.2 s for Diffie-Hellman).
        handle
            .variants(&product(&sym, "WA*WB"))
            .expect("warming variant query");
    }
    let start = Instant::now();
    let answers = match args[3].as_str() {
        "variants" => {
            let terms = args[4].split(';').map(|t| product(&sym, t)).collect();
            handle.variants(&f_app_list(terms)).expect("variants").len()
        }
        op => {
            let eqs: Vec<_> = args[4]
                .split(';')
                .map(|eq| {
                    let (lhs, rhs) = eq.split_once('=').expect("an equation");
                    Equal {
                        lhs: product(&sym, lhs),
                        rhs: product(&sym, rhs),
                    }
                })
                .collect();
            if op == "unify" {
                handle.unify(&eqs).expect("unify").len()
            } else {
                usize::from(handle.unifiable(&eqs).expect("unifiable"))
            }
        }
    };
    println!(
        "{},{},{},{},{:.3},{answers}",
        args[1],
        args[2],
        args[3],
        args[4],
        start.elapsed().as_secs_f64() * 1e3
    );
}
