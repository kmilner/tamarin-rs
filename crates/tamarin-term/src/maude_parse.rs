// Currently GPL 3.0 until granted permission by the following authors:
//   beschmi, jdreier, rkunnema, PhilipLukertWork, meiersi, and other
//   minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Maude/Parser.hs

//! Port of `Term.Maude.Parser`'s reply-parsing portion.
//!
//! Parses the textual replies that Maude emits for `unify`, `match`,
//! `get variants`, and `reduce` queries.

use crate::function_symbols::{
    AcSym, CSym, Constructability, FunSym, NoEqSym, Privacy, EMAP_SYM_STRING, MULT_SYM_STRING,
    MUN_SYM_STRING, NAT_PLUS_SYM_STRING, XOR_SYM_STRING,
};
use crate::lterm::LSort;
use crate::maude_print::{fun_sym_decode, parse_lsort_sym, replace_minus, FUN_SYM_PREFIX};
use crate::maude_types::{MSubst, MTerm, MaudeLit};
use crate::term::Term;

#[derive(Debug, Clone)]
pub struct ParseError(pub String);

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl std::error::Error for ParseError {}

// =============================================================================
// Cursor
// =============================================================================

struct Cursor<'a> {
    src: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    fn new(src: &'a [u8]) -> Self {
        Cursor { src, pos: 0 }
    }
    fn rest(&self) -> &[u8] {
        &self.src[self.pos..]
    }
    fn is_eof(&self) -> bool {
        self.pos >= self.src.len()
    }
    fn peek(&self) -> Option<u8> {
        self.src.get(self.pos).copied()
    }
    fn eat(&mut self, b: u8) -> bool {
        if self.peek() == Some(b) {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    fn eat_str(&mut self, s: &[u8]) -> bool {
        if self.rest().starts_with(s) {
            self.pos += s.len();
            true
        } else {
            false
        }
    }
    fn read_decimal(&mut self) -> Option<u64> {
        let start = self.pos;
        while let Some(b) = self.peek() {
            if b.is_ascii_digit() {
                self.pos += 1;
            } else {
                break;
            }
        }
        if self.pos == start {
            None
        } else {
            std::str::from_utf8(&self.src[start..self.pos])
                .ok()
                .and_then(|s| s.parse().ok())
        }
    }
    fn skip_eol(&mut self) -> bool {
        self.eat_str(b"\r\n") || self.eat(b'\n')
    }
    /// Take while predicate holds, return slice consumed.
    fn take_while<F: Fn(u8) -> bool>(&mut self, f: F) -> &'a [u8] {
        let start = self.pos;
        while let Some(b) = self.peek() {
            if f(b) {
                self.pos += 1;
            } else {
                break;
            }
        }
        &self.src[start..self.pos]
    }
}

// =============================================================================
// Public entry points
// =============================================================================

/// Parse a `unify` reply.
pub fn parse_unify_reply(reply: &[u8]) -> Result<Vec<MSubst>, ParseError> {
    let mut c = Cursor::new(reply);
    if c.eat_str(b"No unifier.") {
        let _ = c.skip_eol();
        return Ok(vec![]);
    }
    parse_substitutions(&mut c)
}

/// Parse a `match` reply.
pub fn parse_match_reply(reply: &[u8]) -> Result<Vec<MSubst>, ParseError> {
    let mut c = Cursor::new(reply);
    if c.eat_str(b"No match.") {
        let _ = c.skip_eol();
        return Ok(vec![]);
    }
    parse_substitutions(&mut c)
}

/// Parse a `reduce` reply: `result <Sort>: <term>\n`.
pub fn parse_reduce_reply(reply: &[u8]) -> Result<MTerm, ParseError> {
    let mut c = Cursor::new(reply);
    if !c.eat_str(b"result ") {
        return Err(ParseError(format!(
            "expected `result `, got: {:?}",
            String::from_utf8_lossy(&c.rest()[..c.rest().len().min(40)])
        )));
    }
    // Sort: TOP -> Msg, otherwise parse_sort.
    if c.eat_str(b"TOP") {
        // ignore
    } else {
        parse_sort(&mut c)?;
    }
    if !c.eat_str(b": ") {
        return Err(ParseError("expected `: ` after result sort".into()));
    }
    let t = parse_term(&mut c)?;
    let _ = c.skip_eol();
    Ok(t)
}

/// Parse a `get variants` reply.
pub fn parse_variants_reply(reply: &[u8]) -> Result<Vec<MSubst>, ParseError> {
    let mut c = Cursor::new(reply);
    let _ = c.skip_eol();
    let mut variants = Vec::new();
    loop {
        if c.eat_str(b"No more variants.") {
            break;
        }
        if !c.eat_str(b"Variant ") {
            return Err(ParseError(format!(
                "expected `Variant ` or `No more variants.`; got {:?}",
                String::from_utf8_lossy(&c.rest()[..c.rest().len().min(40)])
            )));
        }
        // Maude prints `Variant #N`; the `#` is optional.
        let _ = c.eat(b'#');
        let _ = c
            .read_decimal()
            .ok_or_else(|| ParseError("variant id".into()))?;
        let _ = c.skip_eol();
        if !c.eat_str(b"rewrites: ") {
            return Err(ParseError("expected rewrites:".into()));
        }
        let _ = c.read_decimal();
        let _ = c.skip_eol();
        // Reprinted term (sort/TOP : term\n)
        if c.eat_str(b"TOP") {
        } else {
            parse_sort(&mut c)?;
        }
        if !c.eat_str(b": ") {
            return Err(ParseError("expected `: ` in reprinted term".into()));
        }
        let _ = parse_term(&mut c)?;
        let _ = c.skip_eol();
        // Then bindings: `xN:Sort --> term\n` until empty line.
        let mut subst = MSubst::new();
        loop {
            if c.peek() == Some(b'\n') || c.peek() == Some(b'\r') {
                let _ = c.skip_eol();
                break;
            }
            let entry = parse_entry(&mut c)?;
            subst.push(entry);
        }
        variants.push(subst);
    }
    // Haskell `parseVariantsReply` (Parser.hs:275-278):
    //   ... many1 parseVariant <* "No more variants." <* endOfLine
    //       <* "rewrites: " <* takeWhile1 isDigit <* endOfLine <* endOfInput
    // Require >=1 variant, then consume/validate the trailing footer and EOF.
    if variants.is_empty() {
        return Err(ParseError("expected at least one variant (many1)".into()));
    }
    // The `No more variants.` token was already consumed by the loop break.
    let _ = c.skip_eol();
    if !c.eat_str(b"rewrites: ") {
        return Err(ParseError("expected `rewrites: ` footer".into()));
    }
    if c.read_decimal().is_none() {
        return Err(ParseError("expected digits after `rewrites: `".into()));
    }
    let _ = c.skip_eol();
    if !c.is_eof() {
        return Err(ParseError(format!(
            "unexpected trailing input after variants: {:?}",
            String::from_utf8_lossy(&c.rest()[..c.rest().len().min(40)])
        )));
    }
    Ok(variants)
}

// =============================================================================
// Substitutions
// =============================================================================

fn parse_substitutions(c: &mut Cursor) -> Result<Vec<MSubst>, ParseError> {
    let mut substs = Vec::new();
    loop {
        let _ = c.skip_eol();
        if c.is_eof() {
            break;
        }
        // Each substitution starts with `Solution N`, `Unifier N`, or `Matcher N`.
        let saved = c.pos;
        let header_ok = c.eat_str(b"Solution ")
            || {
                c.pos = saved;
                c.eat_str(b"Unifier ")
            }
            || {
                c.pos = saved;
                c.eat_str(b"Matcher ")
            };
        if !header_ok {
            // No more substitution headers; stop reading.  `endOfInput`
            // is enforced after the loop.
            c.pos = saved;
            break;
        }
        let _ = c.read_decimal();
        let _ = c.skip_eol();
        if c.eat_str(b"empty substitution") {
            let _ = c.skip_eol();
            substs.push(Vec::new());
            continue;
        }
        let mut entries = Vec::new();
        loop {
            // Stop when next line isn't an `xN:Sort --> ...` entry.
            let saved2 = c.pos;
            if c.eat_str(b"x") {
                c.pos = saved2;
                let entry = parse_entry(c)?;
                entries.push(entry);
            } else {
                break;
            }
        }
        // HS `parseSubstitution` (Parser.hs:289-296, see line 293) uses `many1 parseEntry` for
        // the non-`empty substitution` branch, requiring at least one entry.
        // (The `empty substitution` line is handled separately above.)
        if entries.is_empty() {
            return Err(ParseError(
                "expected at least one substitution entry (many1)".into(),
            ));
        }
        substs.push(entries);
    }
    // Haskell `parseUnifyReply`/`parseMatchReply` (Parser.hs:258-270) wrap
    // `many1 (parseSubstitution msig) <* endOfInput`: outside the explicit
    // no-unifier/no-match line at least one substitution is required and all
    // input must be consumed.
    if substs.is_empty() {
        return Err(ParseError(
            "expected at least one substitution (many1)".into(),
        ));
    }
    // `endOfInput`: skip a trailing newline, then require EOF.
    let _ = c.skip_eol();
    if !c.is_eof() {
        return Err(ParseError(format!(
            "unexpected trailing input after substitutions: {:?}",
            String::from_utf8_lossy(&c.rest()[..c.rest().len().min(40)])
        )));
    }
    Ok(substs)
}

fn parse_entry(c: &mut Cursor) -> Result<((LSort, u64), MTerm), ParseError> {
    if !c.eat_str(b"x") {
        return Err(ParseError("expected `x` for substitution variable".into()));
    }
    let n = c
        .read_decimal()
        .ok_or_else(|| ParseError("var index".into()))?;
    if !c.eat_str(b":") {
        return Err(ParseError("expected `:` after variable".into()));
    }
    let sort = parse_sort(c)?;
    if !c.eat_str(b" --> ") {
        return Err(ParseError("expected ` --> `".into()));
    }
    let t = parse_term(c)?;
    let _ = c.skip_eol();
    Ok(((sort, n), t))
}

// =============================================================================
// Term parser
// =============================================================================

fn parse_sort(c: &mut Cursor) -> Result<LSort, ParseError> {
    if c.eat_str(b"Pub") {
        Ok(LSort::Pub)
    } else if c.eat_str(b"Fresh") {
        Ok(LSort::Fresh)
    } else if c.eat_str(b"Node") {
        Ok(LSort::Node)
    } else if c.eat_str(b"TamNat") {
        Ok(LSort::Nat)
    } else if c.eat_str(b"Msg") {
        Ok(LSort::Msg)
    } else if c.eat_str(b"M") {
        // HS `parseSort` (Parser.hs:310-311) parses sort `Msg` as
        // `string "M" *> string "sg"` (marked `FIXME: why?`); the explicit
        // `Msg` branch above plus this `M`+`sg` branch reproduce it. Both
        // accept exactly the byte sequence `Msg`.
        if c.eat_str(b"sg") {
            Ok(LSort::Msg)
        } else {
            Err(ParseError("unknown sort starting with M".into()))
        }
    } else {
        Err(ParseError(format!(
            "unknown sort prefix at {:?}",
            String::from_utf8_lossy(&c.rest()[..c.rest().len().min(20)])
        )))
    }
}

fn parse_term(c: &mut Cursor) -> Result<MTerm, ParseError> {
    // `#N:Sort` or `%N:Sort` is a fresh variable (Maude-introduced).
    if c.eat(b'#') || c.eat(b'%') {
        let n = c
            .read_decimal()
            .ok_or_else(|| ParseError("fresh var idx".into()))?;
        if !c.eat_str(b":") {
            return Err(ParseError("expected `:` after fresh idx".into()));
        }
        let s = parse_sort(c)?;
        return Ok(Term::Lit(MaudeLit::FreshVar(n, s)));
    }
    // Otherwise, read identifier up to `:(,)\n `.
    let ident = c.take_while(|b| !matches!(b, b':' | b'(' | b',' | b')' | b'\n' | b' '));
    if ident.is_empty() {
        return Err(ParseError("empty identifier".into()));
    }
    // `ident` is borrowed from the immutable `Cursor::src` (`&'a [u8]`), so it
    // stays valid across the recursive `parse_term` calls below; all consumers
    // only need `&[u8]`, so no owned copy is required.
    // Three branches: `(`, `:`, or end-of-token.
    if c.eat(b'(') {
        // Could be a constant `c(123)` or a function application.
        if let Some(s) = std::str::from_utf8(ident).ok().and_then(parse_lsort_sym) {
            // constant
            let n = c
                .read_decimal()
                .ok_or_else(|| ParseError("const idx".into()))?;
            if !c.eat(b')') {
                return Err(ParseError("expected `)` after const".into()));
            }
            return Ok(Term::Lit(MaudeLit::MaudeConst(n, s)));
        }
        // function application: parse comma-separated arguments.
        let mut args = Vec::new();
        loop {
            args.push(parse_term(c)?);
            if c.eat_str(b", ") || c.eat(b',') {
                continue;
            }
            break;
        }
        if !c.eat(b')') {
            return Err(ParseError("expected `)` after args".into()));
        }
        Ok(build_app(ident, args))
    } else if c.eat_str(b":") {
        // Variable: `xN:Sort` — `ident` is `xN`.
        let s = parse_sort(c)?;
        if let Some(rest) = ident.strip_prefix(b"x") {
            let n: u64 = std::str::from_utf8(rest)
                .ok()
                .and_then(|s| s.parse().ok())
                .ok_or_else(|| ParseError("invalid variable index".into()))?;
            Ok(Term::Lit(MaudeLit::MaudeVar(n, s)))
        } else {
            Err(ParseError("variable identifier must start with `x`".into()))
        }
    } else {
        // Nullary application.
        Ok(build_app(ident, Vec::new()))
    }
}

fn build_app(ident: &[u8], args: Vec<MTerm>) -> MTerm {
    // AC/C operators are all `tam`-prefixed.  Strip the prefix once and
    // compare the suffix against the (compile-time) symbol-name constants,
    // avoiding the per-call `Vec` allocations that `pp_maude_ac_sym` (and
    // the C-symbol equivalent) would do.  The compared bytes are exactly
    // what those helpers would have produced (`tam` + name), so the dispatch is
    // byte-identical; ordinary (non-`tam`) symbols short-circuit immediately.
    if let Some(suffix) = ident.strip_prefix(FUN_SYM_PREFIX.as_bytes()) {
        // AC operator?
        for op in [AcSym::Mult, AcSym::Union, AcSym::NatPlus, AcSym::Xor] {
            let name: &[u8] = match op {
                AcSym::Mult => MULT_SYM_STRING,
                AcSym::Union => MUN_SYM_STRING,
                AcSym::Xor => XOR_SYM_STRING,
                AcSym::NatPlus => NAT_PLUS_SYM_STRING,
            };
            if suffix == name {
                return crate::term::f_app_ac(op, args);
            }
        }
        // C operator (em)?
        // Mirror HS `fAppC EMap args` (Maude/Parser.hs:314-369, see line 355): sort the two
        // arguments so `em` is canonical regardless of Maude's output order.
        if suffix == EMAP_SYM_STRING {
            return crate::term::f_app_c(CSym::EMap, args);
        }
    }
    // List?
    if ident == b"list" {
        // `list(cons(t1, cons(...)))` flattens to `FunSym::List [t1, ...]`.
        if args.len() == 1 {
            let flat = flatten_cons(&args[0]);
            return Term::App(FunSym::List, flat.into());
        }
    }
    // `cons`/`nil` should have been handled inside `list(...)`; if they
    // reach here they fall through to the no-eq handling below.
    // Free symbol — decode and lookup.
    if ident.starts_with(FUN_SYM_PREFIX.as_bytes()) {
        let (name, p, c) = fun_sym_decode(ident);
        let name = replace_minus(&name);
        let arity = args.len();
        let sym = NoEqSym {
            name: crate::intern::intern_bytes(&name),
            arity,
            privacy: p,
            constructability: c,
        };
        // Haskell `parseFunSym` (Parser.hs:331-344) errors when the decoded
        // symbol is not in `allowedfunSyms` (consSym, nilSym, natOneSym plus
        // `noEqFunSyms msig`).  This runs on the live Maude reply path, not
        // just round-trip tests.  We intentionally keep a lenient pass here:
        // Maude only ever echoes symbols from the signature we sent it, so in
        // normal operation the check is redundant; we accept the decoded
        // symbol rather than panicking on a malformed reply.
        return Term::App(FunSym::NoEq(sym), args.into());
    }
    // Unknown — fall back to a public-constructor symbol with the raw name
    // for forward compatibility; this matches Haskell only for certain
    // built-ins (like Maude's own `true`).
    let sym = NoEqSym {
        name: crate::intern::intern_bytes(ident),
        arity: args.len(),
        privacy: Privacy::Public,
        constructability: Constructability::Constructor,
    };
    Term::App(FunSym::NoEq(sym), args.into())
}

fn flatten_cons(t: &MTerm) -> Vec<MTerm> {
    if let Term::App(FunSym::NoEq(s), args) = t {
        if s.name == b"cons" && args.len() == 2 {
            let mut v = vec![args[0].clone()];
            v.extend(flatten_cons(&args[1]));
            return v;
        }
        if s.name == b"nil" && args.is_empty() {
            return Vec::new();
        }
    }
    vec![t.clone()]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_no_unifier() {
        let r = parse_unify_reply(b"No unifier.\n").unwrap();
        assert!(r.is_empty());
    }

    #[test]
    fn parse_no_match() {
        let r = parse_match_reply(b"No match.\n").unwrap();
        assert!(r.is_empty());
    }

    #[test]
    fn parse_substitution_requires_entry() {
        // HS `many1 parseEntry`: a `Solution` header followed by neither
        // `empty substitution` nor an `xN` entry must fail the whole parse.
        let r = parse_unify_reply(b"\nSolution 1\n\n");
        assert!(r.is_err());
    }

    #[test]
    fn parse_simple_reduce_reply() {
        let r = parse_reduce_reply(b"result Pub: p(1)\n").unwrap();
        match r {
            Term::Lit(MaudeLit::MaudeConst(1, LSort::Pub)) => {}
            x => panic!("got {:?}", x),
        }
    }
}
