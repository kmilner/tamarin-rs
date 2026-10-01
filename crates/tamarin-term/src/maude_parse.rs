// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Term.Maude.Parser`'s reply-parsing portion.
//!
//! Parses the textual replies that Maude emits for `unify`, `match`,
//! `get variants`, and `reduce` queries.

use crate::function_symbols::{
    AcFctSym, AcSym, CSym, Constructability, FunSym, NdcState, NoEqSym, Privacy, EMAP_SYM_STRING,
    MULT_SYM_STRING, MUN_SYM_STRING, NAT_PLUS_SYM_STRING, XOR_SYM_STRING,
};
use crate::lterm::LSort;
use crate::maude_print::{
    fun_sym_decode, parse_lsort_sym, replace_minus, ATTR_BLOCK_LEN, FUN_SYM_PREFIX,
};
use crate::maude_sig::MaudeSig;
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
    sig: Option<&'a MaudeSig>,
}

impl<'a> Cursor<'a> {
    fn new(src: &'a [u8]) -> Self {
        Cursor {
            src,
            pos: 0,
            sig: None,
        }
    }
    fn with_sig(src: &'a [u8], sig: &'a MaudeSig) -> Self {
        Cursor {
            src,
            pos: 0,
            sig: Some(sig),
        }
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
    parse_unify_reply_from(&mut c)
}

pub(crate) fn parse_unify_reply_with_sig(
    reply: &[u8],
    sig: &MaudeSig,
) -> Result<Vec<MSubst>, ParseError> {
    let mut c = Cursor::with_sig(reply, sig);
    parse_unify_reply_from(&mut c)
}

fn parse_unify_reply_from(c: &mut Cursor<'_>) -> Result<Vec<MSubst>, ParseError> {
    if c.eat_str(b"No unifier.") {
        let _ = c.skip_eol();
        return Ok(vec![]);
    }
    parse_substitutions(c)
}

/// Parse a `match` reply.
pub fn parse_match_reply(reply: &[u8]) -> Result<Vec<MSubst>, ParseError> {
    let mut c = Cursor::new(reply);
    parse_match_reply_from(&mut c)
}

pub(crate) fn parse_match_reply_with_sig(
    reply: &[u8],
    sig: &MaudeSig,
) -> Result<Vec<MSubst>, ParseError> {
    let mut c = Cursor::with_sig(reply, sig);
    parse_match_reply_from(&mut c)
}

fn parse_match_reply_from(c: &mut Cursor<'_>) -> Result<Vec<MSubst>, ParseError> {
    if c.eat_str(b"No match.") {
        let _ = c.skip_eol();
        return Ok(vec![]);
    }
    parse_substitutions(c)
}

/// Parse a `reduce` reply: `result <Sort>: <term>\n`.
pub fn parse_reduce_reply(reply: &[u8]) -> Result<MTerm, ParseError> {
    let mut c = Cursor::new(reply);
    parse_reduce_reply_from(&mut c)
}

pub(crate) fn parse_reduce_reply_with_sig(
    reply: &[u8],
    sig: &MaudeSig,
) -> Result<MTerm, ParseError> {
    let mut c = Cursor::with_sig(reply, sig);
    parse_reduce_reply_from(&mut c)
}

fn parse_reduce_reply_from(c: &mut Cursor<'_>) -> Result<MTerm, ParseError> {
    if !c.eat_str(b"result ") {
        return Err(ParseError(format!(
            "expected `result `, got: {:?}",
            String::from_utf8_lossy(&c.rest()[..c.rest().len().min(40)])
        )));
    }
    // Sort: `TOP` or a named sort, either way discarded (HS
    // `parseReduceReply` comments "we ignore the sort").
    if !c.eat_str(b"TOP") {
        parse_sort(c)?;
    }
    if !c.eat_str(b": ") {
        return Err(ParseError("expected `: ` after result sort".into()));
    }
    let t = parse_term(c)?;
    let _ = c.skip_eol();
    Ok(t)
}

/// Parse a `get variants` reply.
pub fn parse_variants_reply(reply: &[u8]) -> Result<Vec<MSubst>, ParseError> {
    let mut c = Cursor::new(reply);
    parse_variants_reply_from(&mut c)
}

pub(crate) fn parse_variants_reply_with_sig(
    reply: &[u8],
    sig: &MaudeSig,
) -> Result<Vec<MSubst>, ParseError> {
    let mut c = Cursor::with_sig(reply, sig);
    parse_variants_reply_from(&mut c)
}

fn parse_variants_reply_from(c: &mut Cursor<'_>) -> Result<Vec<MSubst>, ParseError> {
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
        // Reprinted term (`Sort: term` or `[Kind]: term`). Maude brackets
        // the kind when a variant's reprinted subject is ill-sorted, for
        // example `[TOP]: list(...)`.
        let kind = c.eat(b'[');
        if !c.eat_str(b"TOP") {
            parse_sort(c)?;
        }
        if kind && !c.eat(b']') {
            return Err(ParseError("expected `]` after reprinted kind".into()));
        }
        if !c.eat_str(b": ") {
            return Err(ParseError("expected `: ` in reprinted term".into()));
        }
        skip_term(c)?;
        let _ = c.skip_eol();
        // Then bindings: `xN:Sort --> term\n` until empty line.
        let mut subst = MSubst::new();
        loop {
            if c.peek() == Some(b'\n') || c.peek() == Some(b'\r') {
                let _ = c.skip_eol();
                break;
            }
            let entry = parse_entry(c)?;
            subst.push(entry);
        }
        variants.push(subst);
    }
    // Haskell `parseVariantsReply` (Maude/Parser.hs:294-306, see lines 296-298):
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
        // Each substitution starts with `Solution N`, `Unifier N`, or
        // `Matcher N`.  `eat_str` leaves the cursor untouched when it does
        // not match, so the three alternatives can be tried in sequence.
        if !(c.eat_str(b"Solution ") || c.eat_str(b"Unifier ") || c.eat_str(b"Matcher ")) {
            // No more substitution headers; stop reading.  `endOfInput`
            // is enforced after the loop.
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
        // Stop when the next line isn't an `xN:Sort --> ...` entry.
        while c.peek() == Some(b'x') {
            entries.push(parse_entry(c)?);
        }
        // HS `parseSubstitution` (Maude/Parser.hs:309-316, see line 313) uses
        // `many1 parseEntry` for
        // the non-`empty substitution` branch, requiring at least one entry.
        // (The `empty substitution` line is handled separately above.)
        if entries.is_empty() {
            return Err(ParseError(
                "expected at least one substitution entry (many1)".into(),
            ));
        }
        substs.push(entries);
    }
    // Haskell `parseUnifyReply`/`parseMatchReply` (Maude/Parser.hs:278-292) wrap
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
    } else if c.eat_str(b"M") {
        // Transcribed as-is from HS `parseSort` (Maude/Parser.hs:325-331, see lines
        // 330-331), which spells sort `Msg` as `string "M" *> string "sg"`
        // (marked `FIXME: why?`).
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
        Ok(build_app(c.sig, ident, args))
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
        Ok(build_app(c.sig, ident, Vec::new()))
    }
}

/// Consume one term using the same grammar as [`parse_term`] without building
/// an AST. Variant replies repeat the input term before the bindings, and that
/// copy is validation-only.
fn skip_term(c: &mut Cursor) -> Result<(), ParseError> {
    if c.eat(b'#') || c.eat(b'%') {
        c.read_decimal()
            .ok_or_else(|| ParseError("fresh var idx".into()))?;
        if !c.eat_str(b":") {
            return Err(ParseError("expected `:` after fresh idx".into()));
        }
        parse_sort(c)?;
        return Ok(());
    }
    let ident = c.take_while(|b| !matches!(b, b':' | b'(' | b',' | b')' | b'\n' | b' '));
    if ident.is_empty() {
        return Err(ParseError("empty identifier".into()));
    }
    if c.eat(b'(') {
        if std::str::from_utf8(ident)
            .ok()
            .and_then(parse_lsort_sym)
            .is_some()
        {
            c.read_decimal()
                .ok_or_else(|| ParseError("const idx".into()))?;
            if !c.eat(b')') {
                return Err(ParseError("expected `)` after const".into()));
            }
            return Ok(());
        }
        loop {
            skip_term(c)?;
            if c.eat_str(b", ") || c.eat(b',') {
                continue;
            }
            break;
        }
        if !c.eat(b')') {
            return Err(ParseError("expected `)` after args".into()));
        }
    } else if c.eat_str(b":") {
        parse_sort(c)?;
        let Some(rest) = ident.strip_prefix(b"x") else {
            return Err(ParseError("variable identifier must start with `x`".into()));
        };
        if std::str::from_utf8(rest)
            .ok()
            .and_then(|s| s.parse::<u64>().ok())
            .is_none()
        {
            return Err(ParseError("invalid variable index".into()));
        }
    }
    Ok(())
}

fn build_app(sig: Option<&MaudeSig>, ident: &[u8], args: Vec<MTerm>) -> MTerm {
    // AC/C operators are all `tam`-prefixed.  Strip the prefix once and
    // compare the suffix against the (compile-time) symbol-name constants,
    // avoiding the per-call `Vec` allocations that `pp_maude_ac_sym` (and
    // the C-symbol equivalent) would do.  The compared bytes are exactly
    // what those helpers would have produced (`tam` + name), so the dispatch is
    // byte-identical; ordinary (non-`tam`) symbols short-circuit immediately.
    let tam_suffix = ident.strip_prefix(FUN_SYM_PREFIX.as_bytes());
    if let Some(suffix) = tam_suffix {
        // Built-in AC operator?  Guard order follows HS `appIdent`
        // (Maude/Parser.hs:375-386); the names are distinct, so only the pairing
        // matters.
        for (op, name) in [
            (AcSym::Mult, MULT_SYM_STRING),
            (AcSym::Union, MUN_SYM_STRING),
            (AcSym::NatPlus, NAT_PLUS_SYM_STRING),
            (AcSym::Xor, XOR_SYM_STRING),
        ] {
            if suffix == name {
                return crate::term::f_app_ac(op, args);
            }
        }
        if let Some(sym) = sig.and_then(|sig| sig.fun_sym_by_wire(ident)) {
            match sym {
                FunSym::NoEq(sym) if sym.arity == args.len() => {
                    return Term::App(FunSym::NoEq(sym), args.into());
                }
                FunSym::Ac(AcSym::AcFct(sym)) if !args.is_empty() => {
                    return crate::term::f_app_acfct(sym, args);
                }
                _ => {}
            }
        }
        // User-defined AC operator?  HS reaches this guard only from
        // `parseFApp` (Maude/Parser.hs:372-386), i.e. after `(` has been consumed and
        // `sepBy1` has yielded at least one argument; a bare identifier goes to
        // `parseFAppConst` (Maude/Parser.hs:392), which never classifies as AC.  RS
        // keeps that routing.
        //
        // Upstream classifies the identifier by containment —
        // `BC.isInfixOf "tamPDA" ident` and its three siblings
        // (Maude/Parser.hs:379-382) — which also scans the user's own name, so an
        // ordinary non-AC function whose NAME contains a marker (`functions:
        // tamXCAbar/1` -> `tamXCFUtamXCAbar`) is rebuilt as AC: at arity 1
        // `fAppAC _ [a] = a` deletes the application, at arity >= 2 it
        // fabricates a flattened/sorted AC term.  RS classifies by decoding the
        // attribute block instead and deliberately diverges from that upstream
        // bug on exactly those names.
        if !args.is_empty() && is_ac_fct_ident(ident) {
            return crate::term::f_app_acfct(parse_fun_ac_sym(ident), args);
        }
        // C operator (em)?
        // Mirror HS `fAppC EMap args` (Maude/Parser.hs:383): `f_app_c` sorts the two
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
    if tam_suffix.is_some() {
        let (name, p, c, ndc) = fun_sym_decode(ident);
        let name = replace_minus(&name);
        let arity = args.len();
        let sym = NoEqSym {
            name: crate::intern::intern_bytes(&name),
            arity,
            privacy: p,
            constructability: c,
            ndc,
        };
        // Haskell `parseFunSym` (Maude/Parser.hs:351-364) errors when the decoded
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
    // built-ins (like Maude's own `true`).  HS gives the specially-handled
    // idents (`list`, `cons`, `nil`) `(Public, Constructor, NotNDC)` too
    // (`parseFunSym`, Maude/Parser.hs:351-364).
    let sym = NoEqSym {
        name: crate::intern::intern_bytes(ident),
        arity: args.len(),
        privacy: Privacy::Public,
        constructability: Constructability::Constructor,
        ndc: NdcState::NotNdc,
    };
    Term::App(FunSym::NoEq(sym), args.into())
}

/// Is `ident` the Maude encoding of a user-defined AC symbol?
///
/// The encoded layout is `funSymPrefix` (`tam`) + four attribute characters +
/// the user's name (HS `ppMaudeACSym`/`ppMaudeNoEqSym`, Maude/Parser.hs:136-147):
/// privacy `P`/`X`, constructability `C`/`D`, AC state `A`/`F`, NDC state
/// `N`/`U`/`D`/`B`.  Only `ppMaudeACSym` writes `A` in the third slot, so
/// decoding that block is an exact test: `tamXCFUtamXCAbar` (the free symbol
/// `tamXCAbar`) carries `F` and falls through to the free-symbol decode below.
///
/// Upstream instead tests the whole identifier for containment of `tamPDA`,
/// `tamPCA`, `tamXDA` or `tamXCA` (Maude/Parser.hs:379-382), which also scans the
/// name; RS decodes and deliberately diverges there (see the `build_app` AC
/// branch).
fn is_ac_fct_ident(ident: &[u8]) -> bool {
    let Some(rest) = ident.strip_prefix(FUN_SYM_PREFIX.as_bytes()) else {
        return false;
    };
    // `>` not `>=`: the name after the attribute block is never empty.
    rest.len() > ATTR_BLOCK_LEN
        && matches!(rest[0], b'P' | b'X')
        && matches!(rest[1], b'C' | b'D')
        && rest[2] == b'A'
        && matches!(rest[3], b'N' | b'U' | b'D' | b'B')
}

/// HS `parseFunACSym` (Maude/Parser.hs:366-368): decode the attributes out of the
/// Maude identifier and undo the `_` -> `-` renaming applied when it was
/// emitted (`replaceMinusFunAC`).
fn parse_fun_ac_sym(ident: &[u8]) -> AcFctSym {
    let (name, p, c, ndc) = fun_sym_decode(ident);
    AcFctSym::new(replace_minus(&name), p, c, ndc)
}

fn flatten_cons(t: &MTerm) -> Vec<MTerm> {
    // Walk the `cons` spine iteratively: the recursive shape would allocate
    // (and re-copy) one `Vec` per list element.
    let mut out = Vec::new();
    let mut cur = t;
    loop {
        if let Term::App(FunSym::NoEq(s), args) = cur {
            if s.name == b"cons" && args.len() == 2 {
                out.push(args[0].clone());
                cur = &args[1];
                continue;
            }
            if s.name == b"nil" && args.is_empty() {
                return out;
            }
        }
        out.push(cur.clone());
        return out;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn skipped_terms_accept_and_consume_the_parse_term_grammar() {
        for src in [
            &b"x18446744073709551615:Msg"[..],
            b"#3:Fresh",
            b"p(0)",
            b"tamXCFUpair(c(2), tamXCFUfst(x1:Msg))",
            b"list(cons(c(1),cons(%2:Pub,nil)))",
            b"tamXCFUzero",
        ] {
            let mut parsed = Cursor::new(src);
            parse_term(&mut parsed).unwrap();
            let mut skipped = Cursor::new(src);
            skip_term(&mut skipped).unwrap();
            assert_eq!(skipped.pos, parsed.pos, "{}", String::from_utf8_lossy(src));
            assert!(skipped.is_eof());
        }
        for src in [&b"#x:Msg"[..], b"bad:Msg", b"c(x)", b"f(c(1)"] {
            let mut parsed = Cursor::new(src);
            let mut skipped = Cursor::new(src);
            assert_eq!(
                skip_term(&mut skipped).is_err(),
                parse_term(&mut parsed).is_err(),
                "{}",
                String::from_utf8_lossy(src)
            );
        }
    }

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

    /// An identifier carrying the `A` (AC) attribute rebuilds a user-defined
    /// AC application, so the arguments are flattened/sorted by `f_app_ac`
    /// rather than kept in Maude's print order (HS `fAppACfct`).
    #[test]
    fn parse_user_defined_ac_application() {
        let t = parse_reduce_reply(b"result Msg: tamXCAUmy-op(c(2),c(1))\n").unwrap();
        match t {
            Term::App(FunSym::Ac(AcSym::AcFct(s)), args) => {
                assert_eq!(s.name, b"my_op");
                assert_eq!(s.privacy, Privacy::Public);
                assert_eq!(s.constructability, Constructability::Constructor);
                assert_eq!(s.ndc, NdcState::NotNdc);
                assert_eq!(args.len(), 2);
            }
            x => panic!("got {:?}", x),
        }
    }

    /// A bare identifier is a nullary free symbol: HS sends it through
    /// `parseFAppConst` (Maude/Parser.hs:392), which never classifies as AC, so a
    /// free symbol whose own name contains a marker (`functions: tamXCAfoo/0`
    /// encodes to `tamXCFUtamXCAfoo`) stays a `NoEq` constant.  RS keeps that
    /// routing.
    #[test]
    fn parse_nullary_ident_containing_ac_marker() {
        let t = parse_reduce_reply(b"result Msg: tamXCFUtamXCAfoo\n").unwrap();
        match t {
            Term::App(FunSym::NoEq(s), args) => {
                assert_eq!(s.name, b"tamXCAfoo");
                assert_eq!(s.arity, 0);
                assert_eq!(s.privacy, Privacy::Public);
                assert_eq!(s.constructability, Constructability::Constructor);
                assert_eq!(s.ndc, NdcState::NotNdc);
                assert!(args.is_empty());
            }
            x => panic!("got {:?}", x),
        }
    }

    /// The same identifier applied to arguments: upstream reaches `appIdent`'s
    /// containment guards (Maude/Parser.hs:379-382), classifies it as AC, and
    /// `fAppAC _ [a] = a` (Raw.hs:121) deletes the application.  RS decodes
    /// the attribute block instead — the AC slot holds `F` — so the free
    /// symbol `tamXCAfoo/1` survives.  Deliberate divergence from that
    /// upstream bug.
    #[test]
    fn parse_unary_ident_containing_ac_marker_does_not_collapse() {
        let t = parse_reduce_reply(b"result Msg: tamXCFUtamXCAfoo(x1:Msg)\n").unwrap();
        match t {
            Term::App(FunSym::NoEq(s), args) => {
                assert_eq!(s.name, b"tamXCAfoo");
                assert_eq!(s.arity, 1);
                assert_eq!(s.privacy, Privacy::Public);
                assert_eq!(s.constructability, Constructability::Constructor);
                assert_eq!(s.ndc, NdcState::NotNdc);
                assert_eq!(args.len(), 1);
                assert!(matches!(
                    args[0],
                    Term::Lit(MaudeLit::MaudeVar(1, LSort::Msg))
                ));
            }
            x => panic!("got {:?}", x),
        }
    }

    /// At arity >= 2 the same identifier is where upstream's misclassification
    /// fabricates a term: `fAppAC` flattens and SORTS the arguments
    /// (Raw.hs:122-129), so `tamXCAfoo(c(2), c(1))` would come back as an AC
    /// application over `[c(1), c(2)]`.  RS keeps the free symbol and Maude's
    /// argument order.  Deliberate divergence from that upstream bug.
    #[test]
    fn parse_binary_ident_containing_ac_marker_keeps_arg_order() {
        let t = parse_reduce_reply(b"result Msg: tamXCFUtamXCAfoo(c(2), c(1))\n").unwrap();
        match t {
            Term::App(FunSym::NoEq(s), args) => {
                assert_eq!(s.name, b"tamXCAfoo");
                assert_eq!(s.arity, 2);
                assert_eq!(args.len(), 2);
                assert!(matches!(
                    args[0],
                    Term::Lit(MaudeLit::MaudeConst(2, LSort::Msg))
                ));
                assert!(matches!(
                    args[1],
                    Term::Lit(MaudeLit::MaudeConst(1, LSort::Msg))
                ));
            }
            x => panic!("got {:?}", x),
        }
    }

    /// Classifier level: the AC slot of the attribute block decides, not
    /// containment anywhere in the identifier.
    #[test]
    fn ac_fct_ident_classified_by_attr_block() {
        // Real user-AC symbols: `A` in the AC slot, covering each privacy,
        // constructability and NDC letter `funSymEncodeAttr` can emit.
        assert!(is_ac_fct_ident(b"tamXCAUmy-op"));
        assert!(is_ac_fct_ident(b"tamPDANx"));
        assert!(is_ac_fct_ident(b"tamPCADop"));
        assert!(is_ac_fct_ident(b"tamXDABop"));
        // A real user-AC symbol whose NAME also contains a marker: still AC.
        assert!(is_ac_fct_ident(b"tamXCAUtamXCAfoo"));
        // Free symbols whose NAME contains a marker: `F` in the AC slot.
        assert!(!is_ac_fct_ident(b"tamXCFUtamXCAfoo"));
        assert!(!is_ac_fct_ident(b"tamPDFNtamPDAbar"));
        // Built-in operators carry no attribute block at all.
        assert!(!is_ac_fct_ident(b"tammult"));
        assert!(!is_ac_fct_ident(b"tamem"));
        // An attribute block with an empty name is not a symbol.
        assert!(!is_ac_fct_ident(b"tamXCAU"));
        // Identifiers too short to carry a block, and non-`tam` ones.
        assert!(!is_ac_fct_ident(b""));
        assert!(!is_ac_fct_ident(b"tam"));
        assert!(!is_ac_fct_ident(b"tamXCA"));
        assert!(!is_ac_fct_ident(b"XCAUop"));
    }

    /// A real `get variants in MSG : tamXCFUfst(x1:Msg)` reply from Maude
    /// 3.5.1 over the pairing theory.  The fixture keeps the framing that the
    /// handle receives.  `set show timing off` is in force, so `rewrites: N`
    /// carries no timing tail.
    ///
    /// The parser has to walk past several parts of this reply.  There are the
    /// two per-variant headers.  There is the `rewrites:` line.  There is the
    /// reprinted term, which the parser parses and then discards.  There is
    /// the blank line that ends each binding block.  Last there is the
    /// `No more variants.` + `rewrites:` footer of HS `parseVariantsReply`
    /// (Maude/Parser.hs:294-306).  Only the bindings survive.
    #[test]
    fn parse_two_variant_reply() {
        let vs = parse_variants_reply(
            b"\nVariant 1\nrewrites: 0\nMsg: tamXCFUfst(#1:Msg)\n\
              x1:Msg --> #1:Msg\n\
              \nVariant 2\nrewrites: 1\nMsg: %1:Msg\n\
              x1:Msg --> tamXCFUpair(%1:Msg, %2:Msg)\n\
              \nNo more variants.\nrewrites: 1\n",
        )
        .unwrap();
        let pair = |a, b| {
            Term::App(
                FunSym::NoEq(NoEqSym {
                    name: crate::intern::intern_bytes(b"pair"),
                    arity: 2,
                    privacy: Privacy::Public,
                    constructability: Constructability::Constructor,
                    ndc: NdcState::NotNdc,
                }),
                vec![a, b].into(),
            )
        };
        assert_eq!(
            vs,
            vec![
                vec![(
                    (LSort::Msg, 1),
                    Term::Lit(MaudeLit::FreshVar(1, LSort::Msg))
                )],
                vec![(
                    (LSort::Msg, 1),
                    pair(
                        Term::Lit(MaudeLit::FreshVar(1, LSort::Msg)),
                        Term::Lit(MaudeLit::FreshVar(2, LSort::Msg)),
                    )
                )],
            ]
        );
    }

    #[test]
    fn parse_variant_reply_accepts_a_bracketed_kind() {
        let variants = parse_variants_reply(
            b"\nVariant 1\nrewrites: 0\n[TOP]: list(#1:Fresh)\n\
              x0:Fresh --> #1:Fresh\n\
              \nNo more variants.\nrewrites: 0\n",
        )
        .unwrap();
        assert_eq!(variants.len(), 1);
        assert_eq!(variants[0].len(), 1);
    }

    /// The `many1` and `endOfInput` guards of `parse_variants_reply`.  A reply
    /// with no `Variant` block at all is an error.  A reply with a truncated
    /// footer is an error too.  Neither one gives an empty variant list.
    #[test]
    fn parse_variants_reply_requires_a_variant_and_a_footer() {
        assert!(parse_variants_reply(b"\nNo more variants.\nrewrites: 0\n").is_err());
        assert!(parse_variants_reply(
            b"\nVariant 1\nrewrites: 0\nMsg: #1:Msg\nx1:Msg --> #1:Msg\n\nNo more variants.\n"
        )
        .is_err());
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
