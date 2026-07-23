// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, jdreier, and other minor contributors (see upstream git
//   history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs,
//   lib/term/src/Term/Term/FunctionSymbols.hs,
//   lib/term/src/Term/Term/Raw.hs,
//   lib/theory/src/Theory/Model/Formula.hs,
//   lib/theory/src/Theory/Text/Parser/Term.hs,
//   lib/theory/src/Theory/Text/Parser/Token.hs,
//   lib/theory/src/Theory/Tools/Wellformedness.hs, src/Main/Console.hs

//! Faithful port of HS `checkTerms` (the "Formula terms" wellformedness
//! check) from `lib/theory/src/Theory/Tools/Wellformedness.hs:960-985`,
//! together with `formulaTerms` (`:917-920`) and `atomTerms` (`:908-915`).
//!
//! HS `checkTerms header maudeSig fm` collects all terms appearing in the
//! ATOMS of `fm` (via `formulaTerms`), then keeps as offenders every term
//! that is not `allowed`:
//!
//! ```text
//! allowed (Lit (Var (Bound _)))        = True   -- bound (quantified) variable
//! allowed (Lit (Con (Name PubName _))) = True   -- public constant 'c'
//! allowed (FUnion args)                = all allowed args  -- multiset union ++
//! allowed (FApp o args) | o `member` irreducible = all allowed args
//! allowed _                            = False
//!   where irreducible = irreducibleFunSyms maudeSig
//! ```
//!
//! Everything else — free variables, fresh/nat name literals, applications
//! of REDUCIBLE function symbols (sdec/adec/fst/snd/verify/...) — is an
//! offender.  Offenders are rendered with HS's `show` of the `VTerm c
//! (BVar v)` (e.g. `snd(Bound 1)`, `snd(sdec(Bound 3,Bound 2))`, `Free f`).
//!
//! The reducible/irreducible classification is sourced from the REAL
//! computed signature (`MaudeSig::irreducible_fun_syms`), exactly like HS's
//! `irreducibleFunSyms maudeSig`.  Because nullary functions (e.g. a
//! private `f/0`) parse as `Term::Var` in the surface AST, we resolve a
//! bare `Var` whose name+arity matches a signature funsym into an
//! application of that symbol before classifying it (so `K(f)` with
//! `f/0 [private]` is an irreducible `FApp f []`, allowed — matching HS).

use std::collections::{BTreeMap, BTreeSet};

use tamarin_parser::ast as p;
use tamarin_parser::ast::{Atom, BinOp, Formula, SortHint, SuffixSort, Term, VarSpec};
use tamarin_parser::wf::WfError;
use tamarin_term::function_symbols::{AcSym, FunSym};
use tamarin_term::maude_sig::MaudeSig;

use crate::pretty_hpj::{fsep, punctuate, Doc};

/// The fixed render budget for the "Formula terms" WF block, determined
/// empirically from HS output: HS lays the whole `/* WARNING ... */`
/// comment at `lineLength = 110` / `ribbon = 73` (see
/// [`crate::pretty_hpj::LINE_LENGTH`] / [`crate::pretty_hpj::RIBBON`]), but
/// the topic body is rendered already indented inside the surrounding
/// `/* ... */` warning frame, so the effective wrap column for the body is
/// 41 columns narrower than `lineLength`, i.e. 110 - 41 = 69. Boundary
/// verified against the real binary: an offender ending at column 69 stays
/// on the header line, at column 70 it wraps.
///
/// CAVEAT: this is a precomputed effective budget, NOT HS's own lineLength.
/// We do not reproduce the outer warning-frame nesting in the `Doc`
/// renderer, so if HS's `lineWidth` (Console.hs:227-239, see line 236) or the WARNING-frame
/// indentation ever changes, this constant (used at both `render_with`
/// call sites in `render_block`) must be re-derived against the new binary.
const WF_WIDTH: usize = 69;

/// The constant explanatory paragraph (HS `wrappedText "..."`).  The text
/// never varies, so its wrapped form (at `WF_WIDTH`) is constant too.
const ALLOWED_PARAGRAPH: &str = "The only allowed terms are public constants \
    and bound node and message variables. If you encounter free message \
    variables, then you might have forgotten a #-prefix. Sort prefixes can \
    only be dropped where this is unambiguous. Moreover, reducible function \
    symbols are disallowed.";

// =============================================================================
// Resolved term: parser AST resolved against the signature, with De Bruijn
// indices assigned to bound variable uses.  Mirrors HS's `VTerm Name (BVar
// LVar)` shape closely enough to (a) run `allowed` and (b) `show`.
// =============================================================================

/// A function-symbol head.
#[derive(Debug, Clone)]
enum Head {
    /// A NoEq (free) application whose head symbol is `reducible == false`
    /// iff it is in the irreducible set.
    App { name: String, reducible: bool },
    /// An AC function symbol (Union/Mult/Xor/NatPlus).  `reducible` is set
    /// from the signature's irreducible AC set, EXCEPT Union which HS
    /// special-cases as always-allowed-if-args-allowed (`FUnion`).
    Ac { sym: AcSym, reducible: bool },
}

/// A resolved term in De-Bruijn form, sufficient to evaluate `allowed` and
/// to `show` like HS.
#[derive(Debug, Clone)]
enum RTerm {
    /// A bound variable: `Bound n`.
    Bound(u32),
    /// A free variable: `Free <lvar-rendering>`.
    Free(VarSpec),
    /// A public constant `'c'` (HS `Con (Name PubName _)`).
    PubConst(String),
    /// A fresh-name literal `~'n'` (HS `Con (Name FreshName _)`).
    FreshConst(String),
    /// A nat-name literal `%'n'` (HS `Con (Name NatName _)`).
    NatConst(String),
    /// An application `head(args)`.
    App(Head, Vec<RTerm>),
}

// =============================================================================
// Signature lookup
// =============================================================================

/// Index of irreducible function symbols by (name, arity).  Mirrors
/// `irreducibleFunSyms maudeSig` membership tests.
struct Irreducible {
    /// Arities (keyed by name-bytes) of every irreducible NoEq symbol.
    noeq: BTreeMap<Vec<u8>, BTreeSet<usize>>,
    /// Irreducible AC symbols (e.g. `Mult`, `NatPlus` are irreducible; `Xor`
    /// is reducible).  HS keys on the `FunSym` value, which for AC ops is
    /// `AC <ACSym>`.
    ac: BTreeSet<AcSym>,
    /// Names of all nullary NoEq symbols in the FULL signature.  Used to
    /// resolve a bare `Var` whose name is a declared nullary funsym into an
    /// application (mirrors HS resolving `f/0` to `FApp f []`).
    nullary_names: BTreeSet<Vec<u8>>,
}

impl Irreducible {
    fn from_sig(sig: &MaudeSig) -> Self {
        let mut noeq: BTreeMap<Vec<u8>, BTreeSet<usize>> = BTreeMap::new();
        let mut ac = BTreeSet::new();
        for s in &sig.irreducible_fun_syms {
            match s {
                FunSym::NoEq(n) => {
                    noeq.entry(n.name.to_vec()).or_default().insert(n.arity);
                }
                FunSym::Ac(a) => {
                    ac.insert(*a);
                }
                _ => {}
            }
        }
        let mut nullary_names = BTreeSet::new();
        for s in sig.fun_syms.iter() {
            if let FunSym::NoEq(n) = s {
                if n.arity == 0 {
                    nullary_names.insert(n.name.to_vec());
                }
            }
        }
        Irreducible {
            noeq,
            ac,
            nullary_names,
        }
    }

    /// Is the NoEq symbol `name/arity` irreducible?
    fn is_irreducible(&self, name: &str, arity: usize) -> bool {
        self.noeq
            .get(name.as_bytes())
            .is_some_and(|s| s.contains(&arity))
    }

    /// Is the AC symbol `a` irreducible?
    fn is_ac_irreducible(&self, a: AcSym) -> bool {
        self.ac.contains(&a)
    }

    /// Is `name` a declared nullary funsym?
    fn nullary_named(&self, name: &str) -> bool {
        self.nullary_names.contains(name.as_bytes())
    }
}

// =============================================================================
// Public entry point
// =============================================================================

/// Port of HS `formulaReports`'s `checkTerms` arm (Wellformedness.hs:999-1014, see line 1003),
/// for every lemma + restriction formula (in theory order, lemmas before
/// restrictions — HS `annFormulas`).  Macros must already be expanded by
/// the caller (HS applies `applyMacroInFormula` first).
pub fn check_terms_wf(thy: &p::Theory, sig: &MaudeSig) -> Vec<WfError> {
    let irr = Irreducible::from_sig(sig);
    let mut out = Vec::new();

    // HS folds surplus args of an arity-1 function into a pair at PARSE time
    // (`naryOpApp` `k == 1`, Theory/Text/Parser/Term.hs:84-87), so the AST the
    // wf check inspects already carries `h(<a, b>)` (an irreducible `h/1`
    // applied to a pair), NOT `h(a, b)`.  RS's arity-unaware parser keeps the
    // surplus args, so without this fold a unary `h(a, b)` resolves to a
    // non-existent reducible `h/2` and is spuriously flagged "uses terms of
    // the wrong form: reducible function symbols are disallowed".  Fold first
    // (mirrors the lemma/restriction pretty-printer in pretty_theory.rs).
    let arity1 = crate::elaborate::arity1_noeq_names(sig);

    // HS `annFormulas = lemmas <|> restrictions` — all lemmas (theory
    // order) then all restrictions (theory order).
    let mut lemmas: Vec<(String, Formula)> = Vec::new();
    let mut restrictions: Vec<(String, Formula)> = Vec::new();
    for item in &thy.items {
        match item {
            p::TheoryItem::Lemma(l) => lemmas.push((
                format!("Lemma `{}'", l.name),
                crate::elaborate::rewrite_arity1_formula(&l.formula, &arity1),
            )),
            p::TheoryItem::Restriction(r) | p::TheoryItem::LegacyAxiom(r) => restrictions.push((
                format!("Restriction `{}'", r.name),
                crate::elaborate::rewrite_arity1_formula(&r.formula, &arity1),
            )),
            _ => {}
        }
    }
    for (header, fm) in lemmas.into_iter().chain(restrictions) {
        if let Some(msg) = check_one(&header, &fm, &irr) {
            out.push(WfError::new("Formula terms", msg));
        }
    }
    out
}

/// Run `checkTerms` for a single annotated formula.  Returns the formatted
/// WF block (matching HS byte-for-byte) iff there are offenders.
fn check_one(header: &str, fm: &Formula, irr: &Irreducible) -> Option<String> {
    let mut terms: Vec<RTerm> = Vec::new();
    collect_formula_terms(fm, &mut Vec::new(), irr, &mut terms);

    let offenders: Vec<String> = terms
        .iter()
        .filter(|t| !allowed(t))
        .map(show_rterm)
        .collect();

    if offenders.is_empty() {
        return None;
    }
    Some(render_block(header, &offenders))
}

// =============================================================================
// formulaTerms / atomTerms with De-Bruijn assignment
// =============================================================================

/// A binder in scope, tracked for De-Bruijn assignment.  `scope[0]` is the
/// OUTERMOST binder; `scope[last]` the innermost.  The De-Bruijn index of a
/// binder at position `i` is `scope.len() - 1 - i` (count of binders inner
/// to it).
type Scope = Vec<VarSpec>;

/// HS `formulaTerms`: collect the terms from every atom.  Recurses through
/// connectives and quantifiers, pushing binders onto `scope` so that
/// variable uses inside the body get the right De-Bruijn index.
fn collect_formula_terms(fm: &Formula, scope: &mut Scope, irr: &Irreducible, out: &mut Vec<RTerm>) {
    match fm {
        Formula::True | Formula::False => {}
        Formula::Atom(a) => collect_atom_terms(a, scope, irr, out),
        Formula::Not(g) => collect_formula_terms(g, scope, irr, out),
        Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) | Formula::Iff(a, b) => {
            collect_formula_terms(a, scope, irr, out);
            collect_formula_terms(b, scope, irr, out);
        }
        Formula::Forall(vs, body) | Formula::Exists(vs, body) => {
            // HS `foldr (hinted q) f vs` quantifies the LAST var innermost.
            // Pushing in source order makes the last-listed var the
            // innermost binder (highest scope position) — exactly the
            // De-Bruijn nesting HS produces.
            let pushed = vs.len();
            for v in vs {
                scope.push(v.clone());
            }
            collect_formula_terms(body, scope, irr, out);
            for _ in 0..pushed {
                scope.pop();
            }
        }
    }
}

/// HS `atomTerms` — the terms a single atom contributes.
fn collect_atom_terms(a: &Atom, scope: &Scope, irr: &Irreducible, out: &mut Vec<RTerm>) {
    match a {
        // Action i fa  ->  i : factTerms fa   (temporal var THEN fact args)
        Atom::Action(fact, tp) => {
            out.push(resolve_term(tp, scope, irr, TermPos::Temporal));
            for arg in &fact.args {
                out.push(resolve_term(arg, scope, irr, TermPos::Message));
            }
        }
        // EqE t s -> [t, s]
        Atom::Eq(x, y) => {
            out.push(resolve_term(x, scope, irr, TermPos::Message));
            out.push(resolve_term(y, scope, irr, TermPos::Message));
        }
        // Subterm i j -> [i, j]
        Atom::Subterm(x, y) => {
            out.push(resolve_term(x, scope, irr, TermPos::Message));
            out.push(resolve_term(y, scope, irr, TermPos::Message));
        }
        // Less i j -> [i, j]  (temporal node vars)
        Atom::Less(x, y) => {
            out.push(resolve_term(x, scope, irr, TermPos::Temporal));
            out.push(resolve_term(y, scope, irr, TermPos::Temporal));
        }
        // The multiset-`(<)` ordering relation: operands are message terms.
        Atom::LessMset(x, y) => {
            out.push(resolve_term(x, scope, irr, TermPos::Message));
            out.push(resolve_term(y, scope, irr, TermPos::Message));
        }
        // Last i -> [i]  (temporal)
        Atom::Last(tp) => {
            out.push(resolve_term(tp, scope, irr, TermPos::Temporal));
        }
        // Syntactic (predicate) atoms contribute no real terms
        // (HS `atomTerms (Syntactic _) = []`).
        Atom::Pred(_) => {}
    }
}

/// The syntactic position of a term, which fixes the implicit sort of an
/// untagged variable use (mirrors the parser's positional sort inference).
#[derive(Clone, Copy, PartialEq)]
enum TermPos {
    /// Argument of `@`, `<`, `last` — implicitly a node (temporal) var.
    Temporal,
    /// A message-position term (fact arg, equality operand, ...).
    Message,
}

// =============================================================================
// Term resolution: parser AST -> RTerm (with De-Bruijn + signature lookup)
// =============================================================================

fn resolve_term(t: &Term, scope: &Scope, irr: &Irreducible, pos: TermPos) -> RTerm {
    match t {
        Term::Var(v) => resolve_var(v, scope, irr, pos),
        Term::PubLit(s) => RTerm::PubConst(s.clone()),
        Term::FreshLit(s) => RTerm::FreshConst(s.clone()),
        Term::NatLit(s) => RTerm::NatConst(s.clone()),
        // Bare numeric/`1`/`%1` literals: HS treats these as nullary
        // irreducible Public constructors.  The DH `1` is `oneSymString =
        // "one"` and the nat `%1` is `natOneSymString = "tone"`
        // (FunctionSymbols.hs:134-134,144); both are arity-0 Public Constructors
        // and hence always `allowed`, so the head name is never rendered as
        // an offender — but we still use the HS-faithful names here.
        Term::Number(n) => RTerm::PubConst(n.to_string()),
        Term::NumberOne => RTerm::App(
            Head::App {
                name: "one".into(),
                reducible: false,
            },
            vec![],
        ),
        Term::NatOne => RTerm::App(
            Head::App {
                name: "tone".into(),
                reducible: false,
            },
            vec![],
        ),
        Term::DhNeutral => RTerm::App(
            Head::App {
                name: "DH_neutral".into(),
                reducible: false,
            },
            vec![],
        ),
        Term::App(name, args) => resolve_app(name, args, scope, irr),
        Term::AlgApp(name, a, b) => {
            // `op{a}b` == `op(a, b)`.
            let args = vec![
                resolve_term(a, scope, irr, TermPos::Message),
                resolve_term(b, scope, irr, TermPos::Message),
            ];
            resolve_named(name, args, irr)
        }
        Term::Pair(items) => {
            // `<a, b, c>` is right-nested `pair(a, pair(b, c))`.
            let resolved: Vec<RTerm> = items
                .iter()
                .map(|i| resolve_term(i, scope, irr, TermPos::Message))
                .collect();
            build_pair(resolved, irr)
        }
        Term::Diff(a, b) => {
            let args = vec![
                resolve_term(a, scope, irr, TermPos::Message),
                resolve_term(b, scope, irr, TermPos::Message),
            ];
            resolve_named("diff", args, irr)
        }
        Term::BinOp(op, a, b) => {
            let ra = resolve_term(a, scope, irr, TermPos::Message);
            let rb = resolve_term(b, scope, irr, TermPos::Message);
            match op {
                // `^` (exp) is a NoEq symbol; the rest are AC symbols.
                BinOp::Exp => resolve_named("exp", vec![ra, rb], irr),
                BinOp::Union => resolve_ac(AcSym::Union, vec![ra, rb], irr),
                BinOp::Mult => resolve_ac(AcSym::Mult, vec![ra, rb], irr),
                BinOp::Xor => resolve_ac(AcSym::Xor, vec![ra, rb], irr),
                BinOp::NatPlus => resolve_ac(AcSym::NatPlus, vec![ra, rb], irr),
            }
        }
        Term::PatMatch(inner) => resolve_term(inner, scope, irr, pos),
    }
}

fn resolve_app(name: &str, args: &[Term], scope: &Scope, irr: &Irreducible) -> RTerm {
    let resolved: Vec<RTerm> = args
        .iter()
        .map(|a| resolve_term(a, scope, irr, TermPos::Message))
        .collect();
    resolve_named(name, resolved, irr)
}

/// Build a NoEq application node from a name + already-resolved args,
/// classifying the head as reducible/irreducible from the real signature.
fn resolve_named(name: &str, args: Vec<RTerm>, irr: &Irreducible) -> RTerm {
    let arity = args.len();
    let reducible = !irr.is_irreducible(name, arity);
    RTerm::App(
        Head::App {
            name: name.to_string(),
            reducible,
        },
        args,
    )
}

/// Build an AC application node, classifying via the irreducible AC set.
/// Union is HS-special-cased (`FUnion` — always allowed-if-args-allowed)
/// so we force `reducible = false` for it regardless of set membership.
fn resolve_ac(sym: AcSym, args: Vec<RTerm>, irr: &Irreducible) -> RTerm {
    let reducible = if matches!(sym, AcSym::Union) {
        false
    } else {
        !irr.is_ac_irreducible(sym)
    };
    RTerm::App(Head::Ac { sym, reducible }, args)
}

/// Right-nested pair construction matching HS's `<a,b,c> = pair(a, pair(b,
/// c))`.  `pair` is irreducible.
fn build_pair(mut items: Vec<RTerm>, irr: &Irreducible) -> RTerm {
    if items.is_empty() {
        return resolve_named("pair", vec![], irr);
    }
    if items.len() == 1 {
        return items.pop().unwrap();
    }
    let head = items.remove(0);
    let rest = build_pair(items, irr);
    resolve_named("pair", vec![head, rest], irr)
}

/// Resolve a variable USE to either a `Bound n` (if a matching binder is in
/// scope) or `Free` (otherwise) — UNLESS the name is a declared nullary
/// function symbol with no matching binder, in which case it is an
/// irreducible `FApp name []` (HS resolves `f/0` to `FApp f []`).
fn resolve_var(v: &VarSpec, scope: &Scope, irr: &Irreducible, pos: TermPos) -> RTerm {
    if let Some(idx) = lookup_bound(v, scope, pos) {
        return RTerm::Bound(idx);
    }
    // Not bound: a bare untagged name that is a declared nullary funsym
    // is an application (e.g. private `f/0` parsed as Var("f")).
    if matches!(v.sort, SortHint::Untagged) && irr.nullary_named(&v.name) {
        return resolve_named(&v.name, vec![], irr);
    }
    RTerm::Free(v.clone())
}

/// Find the innermost binder matching `v` and return its De-Bruijn index.
///
/// HS binds a use to its binder via full `LVar` equality — name AND sort AND
/// idx (`quantify x = ... | v == x = Bound i`, Formula.hs:340-345; `LVar` `Eq`
/// compares `idx`, sort and name, LTerm.hs:516-517). We reproduce this exactly
/// on the sort-*kind*: the use's sort is concrete in HS, never approximate.
/// The parser assigns every variable a concrete `LSort` before `quantify`
/// runs (Formula.hs:114-119 `standardFormula msgvar nodevar`):
///   - a message-position variable is parsed by `msgvar`
///     (`sortedLVar [LSortFresh, LSortPub, LSortNat, LSortMsg]`,
///     Token.hs:440-441), so an *untagged* message use takes the
///     `mkPrefixParser LSortMsg` arm (the bare `LSortMsg -> pure ()` case,
///     Token.hs:424-426) and gets the concrete sort `LSortMsg` — hence
///     `kind_of(SortHint::Untagged) == KIND_MSG` is exact, not approximate;
///   - a temporal-position variable is parsed by `nodevar`
///     (`LSortNode`, Token.hs:444-447), hence `KIND_NODE`.
///
/// `quantify`'s `v == x` then compares sort exactly, so an untagged `x` binds
/// only to a `LSortMsg` binder, never to a `~x`/`$x`/`%x`/`#x` binder of the
/// same name+idx. The `idx` comparison likewise keeps `x.1` and `x.2` distinct.
fn lookup_bound(v: &VarSpec, scope: &Scope, pos: TermPos) -> Option<u32> {
    // The use's concrete sort-kind (Temporal positions are LSortNode; message
    // positions take the use's sigil, or LSortMsg when untagged — see above).
    let expected: u8 = match pos {
        TermPos::Temporal => KIND_NODE,
        TermPos::Message => kind_of(&v.sort),
    };
    // Search innermost (last) first.
    for (i, b) in scope.iter().enumerate().rev() {
        if b.name != v.name || b.idx != v.idx {
            continue;
        }
        if kind_of(&b.sort) == expected {
            let db = (scope.len() - 1 - i) as u32;
            return Some(db);
        }
    }
    None
}

const KIND_FRESH: u8 = 0;
const KIND_PUB: u8 = 1;
const KIND_NODE: u8 = 2;
const KIND_NAT: u8 = 3;
const KIND_MSG: u8 = 4;

fn kind_of(s: &SortHint) -> u8 {
    match s {
        SortHint::Fresh | SortHint::Suffix(SuffixSort::Fresh) => KIND_FRESH,
        SortHint::Pub | SortHint::Suffix(SuffixSort::Pub) => KIND_PUB,
        SortHint::Node | SortHint::Suffix(SuffixSort::Node) => KIND_NODE,
        SortHint::Nat | SortHint::Suffix(SuffixSort::Nat) => KIND_NAT,
        SortHint::Msg | SortHint::Suffix(SuffixSort::Msg) => KIND_MSG,
        SortHint::Untagged => KIND_MSG,
    }
}

// =============================================================================
// `allowed` predicate (HS Wellformedness.hs:978-985)
// =============================================================================

fn allowed(t: &RTerm) -> bool {
    match t {
        RTerm::Bound(_) => true,
        RTerm::PubConst(_) => true,
        RTerm::App(Head::App { reducible, .. }, args)
        | RTerm::App(Head::Ac { reducible, .. }, args) => !*reducible && args.iter().all(allowed),
        // Free vars, fresh/nat name constants -> offenders.
        RTerm::Free(_) | RTerm::FreshConst(_) | RTerm::NatConst(_) => false,
    }
}

// =============================================================================
// `show` of an offender term (HS `Show (VTerm Name (BVar LVar))`)
// =============================================================================

fn show_rterm(t: &RTerm) -> String {
    let mut s = String::new();
    write_rterm(t, &mut s);
    s
}

fn write_rterm(t: &RTerm, out: &mut String) {
    match t {
        RTerm::Bound(n) => {
            out.push_str("Bound ");
            out.push_str(&n.to_string());
        }
        RTerm::Free(v) => {
            out.push_str("Free ");
            out.push_str(&show_lvar(v));
        }
        // HS `Show Name`: PubName -> `'n'`, FreshName -> `~'n'`,
        // NatName -> `%'n'`.
        RTerm::PubConst(n) => {
            out.push('\'');
            out.push_str(n);
            out.push('\'');
        }
        RTerm::FreshConst(n) => {
            out.push_str("~'");
            out.push_str(n);
            out.push('\'');
        }
        RTerm::NatConst(n) => {
            out.push_str("%'");
            out.push_str(n);
            out.push('\'');
        }
        RTerm::App(head, args) => {
            // HS `Show (Term a)` (Term/Raw.hs:219-227):
            //   FApp (NoEq (s,_)) [] -> s
            //   FApp (NoEq (s,_)) as -> s ++ "(" ++ intercalate "," ... ++ ")"
            //   FApp (AC o) as       -> show o ++ "(" ++ ... ++ ")"
            // ACSym derives Show as the constructor name (Union/Mult/Xor/NatPlus).
            let name: &str = match head {
                Head::App { name, .. } => name.as_str(),
                Head::Ac { sym, .. } => match sym {
                    AcSym::Union => "Union",
                    AcSym::Mult => "Mult",
                    AcSym::Xor => "Xor",
                    AcSym::NatPlus => "NatPlus",
                },
            };
            out.push_str(name);
            if !args.is_empty() {
                out.push('(');
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    write_rterm(a, out);
                }
                out.push(')');
            }
        }
    }
}

/// HS `Show LVar`: `sortPrefix s ++ body`, where body is the name (or, if
/// `idx /= 0`, `name.idx`; if the name is empty, just the index).
/// Shared with the message-derivation probe (`deriv_check`).
pub(crate) fn show_lvar(v: &VarSpec) -> String {
    let prefix = match v.sort {
        SortHint::Fresh | SortHint::Suffix(SuffixSort::Fresh) => "~",
        SortHint::Pub | SortHint::Suffix(SuffixSort::Pub) => "$",
        SortHint::Node | SortHint::Suffix(SuffixSort::Node) => "#",
        SortHint::Nat | SortHint::Suffix(SuffixSort::Nat) => "%",
        _ => "",
    };
    let body = if v.name.is_empty() {
        v.idx.to_string()
    } else if v.idx == 0 {
        v.name.clone()
    } else {
        format!("{}.{}", v.name, v.idx)
    };
    format!("{}{}", prefix, body)
}

// =============================================================================
// Block rendering (matches HS prettyWfErrorReport per-topic body)
// =============================================================================

/// Build the full "Formula terms" topic block (underline header + offender
/// fsep line + blank `$--$` line + wrapped paragraph), byte-identical to HS.
fn render_block(header: &str, offenders: &[String]) -> String {
    // fsep $ (text "<header> uses terms of the wrong form:")
    //       : punctuate comma (map (nest 2 . text . quote . show) offenders)
    let mut items = vec![Doc::text(format!(
        "{} uses terms of the wrong form:",
        header
    ))];
    let off_docs: Vec<Doc> = offenders
        .iter()
        .map(|o| Doc::text(format!("`{}'", o)).nest(2))
        .collect();
    items.extend(punctuate(Doc::text(","), off_docs));
    let line1 = fsep(items).nest(2).render_with(WF_WIDTH, WF_WIDTH);

    let words: Vec<Doc> = ALLOWED_PARAGRAPH
        .split_whitespace()
        .map(Doc::text)
        .collect();
    let para = fsep(words).nest(2).render_with(WF_WIDTH, WF_WIDTH);

    let mut out = String::new();
    out.push_str("Formula terms\n=============\n");
    out.push('\n'); // HS `$-$` blank line before the nest-2 body
    out.push_str(&line1);
    out.push('\n');
    out.push_str("  \n"); // HS `$--$` blank line (nest-2 `text ""`)
    out.push_str(&para);
    out
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_parser::parse_theory;

    fn sig_of(src: &str) -> (p::Theory, MaudeSig) {
        let mut thy = parse_theory(src, &[]).expect("parse");
        crate::macro_expand::expand_theory_macros(&mut thy);
        let elab = crate::elaborate::elaborate(&thy).expect("elaborate");
        let sig = elab.signature.maude_sig.clone();
        (thy, sig)
    }

    #[test]
    fn private_nullary_function_is_allowed() {
        // secretF reproducer: `f/0 [private]`, lemma `All #i. K(f) @ i ==> F`.
        let src = "theory T begin\n\
                   functions: f/0 [private]\n\
                   lemma secretF:\n  \"All #i. K(f) @ i ==> F\"\n\
                   end\n";
        let (thy, sig) = sig_of(src);
        let report = check_terms_wf(&thy, &sig);
        assert!(report.is_empty(), "expected no offenders, got {:?}", report);
    }

    #[test]
    fn reducible_destructor_is_offender() {
        // type_assertion-style: `snd`/`sdec` are reducible destructors.
        let src = "theory T begin\n\
                   builtins: symmetric-encryption\n\
                   lemma L:\n\
                     \"All x #i. K(x) @ i ==> Ex body key #j #k. \
                       K(body) @ j & key = snd(sdec(body, key)) & j < i & k < i\"\n\
                   end\n";
        let (thy, sig) = sig_of(src);
        let report = check_terms_wf(&thy, &sig);
        assert_eq!(report.len(), 1, "expected one Formula-terms block");
        let msg = &report[0].message;
        assert!(
            msg.contains("`snd(sdec(Bound 3,Bound 2))'"),
            "offender rendering mismatch:\n{}",
            msg
        );
    }

    #[test]
    fn plain_protocol_lemma_no_offenders() {
        let src = "theory T begin\n\
                   lemma L:\n  \"All x #i. K(x) @ i ==> Ex #j. K(x) @ j\"\n\
                   end\n";
        let (thy, sig) = sig_of(src);
        assert!(check_terms_wf(&thy, &sig).is_empty());
    }

    #[test]
    fn public_constant_allowed() {
        let src = "theory T begin\n\
                   lemma L:\n  \"All #i. K('c') @ i ==> F\"\n\
                   end\n";
        let (thy, sig) = sig_of(src);
        assert!(check_terms_wf(&thy, &sig).is_empty());
    }

    #[test]
    fn unary_hash_with_surplus_args_is_allowed() {
        // `hashing` gives `h/1`.  Surface `h(x, y)` is folded to `h(<x, y>)`
        // (an irreducible `h/1` applied to a pair) at parse time in HS
        // (naryOpApp k==1) — so it is ALLOWED, not flagged as a reducible
        // `h/2`.  This is the alethea selectionphase root.
        let src = "theory T begin\n\
                   builtins: hashing\n\
                   lemma L:\n  \"All x y #i. K(h(x, y)) @ i ==> F\"\n\
                   end\n";
        let (thy, sig) = sig_of(src);
        let report = check_terms_wf(&thy, &sig);
        assert!(report.is_empty(), "expected no offenders, got {:?}", report);
    }

    #[test]
    fn untagged_message_use_does_not_bind_to_node_binder() {
        // An untagged message-position use `x` must NOT bind to a `#x` node
        // binder of the same name+idx: HS's `LVar` Eq compares sort, and the
        // parser gives an untagged message use the concrete sort `LSortMsg`,
        // so `quantify`'s `v == x` fails and the use stays `Free x`.
        //
        // Verified against the v1.13.0 binary on
        //   lemma L: "All #x. (K(x) @ #x) ==> F"
        // which prints `Lemma `L' uses terms of the wrong form: `Free x'`.
        let src = "theory T begin\n\
                   lemma L:\n  \"All #x. (K(x) @ #x) ==> F\"\n\
                   end\n";
        let (thy, sig) = sig_of(src);
        let report = check_terms_wf(&thy, &sig);
        assert_eq!(report.len(), 1, "expected one Formula-terms block");
        assert!(
            report[0].message.contains("`Free x'"),
            "untagged use must stay Free (not bind to #x), got:\n{}",
            report[0].message
        );
    }

    #[test]
    fn free_message_variable_is_offender() {
        // A msg var used but never quantified -> Free offender.
        let src = "theory T begin\n\
                   lemma L:\n  \"All #i. K(x) @ i ==> F\"\n\
                   end\n";
        let (thy, sig) = sig_of(src);
        let report = check_terms_wf(&thy, &sig);
        assert_eq!(report.len(), 1);
        assert!(
            report[0].message.contains("`Free x'"),
            "got: {}",
            report[0].message
        );
    }
}
