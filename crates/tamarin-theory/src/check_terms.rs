// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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
//!
//! # AC/C canonicalisation, and why it happens after De Bruijn assignment
//!
//! HS terms reach `checkTerms` in AC-normal form: every application node is
//! built by the smart constructor `fApp` (`Term/Term/Raw.hs:110-136`), which
//! splices nested same-symbol arguments and sorts them for an AC symbol
//! (`fAppAC`) and sorts the argument list for a C symbol (`fAppC`).  The
//! sort key is the derived `Ord` of `Term (Lit Name (BVar LVar))`, and the
//! ordering is re-established on the BOUND form: `quantify`
//! (`Theory/Model/Formula.hs:347-352`) rewrites a free variable to
//! `Bound i` through `mapLits` (`:288-291`), which rebuilds every node with
//! `fApp` and therefore re-sorts it.  The outermost binder's pass runs last
//! and sees every lit in its final form, so the term the checker inspects is
//! sorted by the POST-De-Bruijn ordering — under which `Bound` precedes
//! every `Free` and `Bound i` orders by `i`.  [`resolve_term`] therefore
//! builds `RTerm`s bottom-up with final De Bruijn indices already assigned
//! and canonicalises at each node, and [`cmp_rterm`] is the sort key.

use std::collections::{BTreeMap, BTreeSet};

use tamarin_parser::ast as p;
use tamarin_parser::ast::{Atom, BinOp, Formula, SortHint, SuffixSort, Term, VarSpec};
use tamarin_parser::wf::WfError;
use tamarin_term::function_symbols::{AcFctSym, AcSym, CSym, FunSym, EMAP_SYM_STRING};
use tamarin_term::maude_sig::MaudeSig;

use crate::pretty_hpj::{fsep, punctuate, Doc};

/// The fixed render budget for the formula-report WF blocks, determined
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
/// renderer, so if HS's `lineWidth` (Console.hs:242-243) or the WARNING-frame
/// indentation ever changes, this constant (used at both `render_with`
/// call sites in `render_block` and by
/// [`crate::formula_reports`]'s "Quantifier sorts" block, which HS lays out
/// inside the same frame) must be re-derived against the new binary.
pub(crate) const WF_WIDTH: usize = 69;

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
    /// An AC function symbol (Union/Mult/Xor/NatPlus, or a user-declared
    /// `[AC]` symbol).  `reducible` is set from the signature's irreducible
    /// AC set, EXCEPT Union which HS special-cases as
    /// always-allowed-if-args-allowed (`FUnion`).
    Ac { sym: AcSym, reducible: bool },
    /// A C (commutative, not associative) function symbol — `em`, HS's only
    /// one.  It carries no `reducible` flag because it is never irreducible:
    /// `C EMap` enters the signature only with `bilinear-pairing`, and
    /// `bpReducibleFunSig` subtracts it again when it does
    /// (`Term/Term/FunctionSymbols.hs:311-312`, `Term/Maude/Signature.hs:120-124`),
    /// so the `S.member irreducible` guard of `allowed` fails either way.
    C(CSym),
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
    /// Every user-declared `[AC]` symbol of the FULL signature, keyed by name.
    /// The INFIX spelling of such a symbol is always `fAppAC (ACfct …)` (HS
    /// `acterm`, Theory/Text/Parser/Term.hs:166-172); the prefix and `op{a}b`
    /// spellings are too (`naryOpApp` `:104-105`, `binaryAlgApp` `:120-121`)
    /// UNLESS the name is also a `NoEq` symbol of the full signature — see
    /// [`Irreducible::prefix_ac_fct`] — so the checker's term view builds the
    /// same flattened, sorted AC node exactly where HS does.
    ac_fct_syms: BTreeMap<Vec<u8>, AcFctSym>,
    /// Names (any arity) of every NoEq symbol of the FULL signature — HS
    /// `noEqFunSyms maudeSig` over `funSyms` (Term/Maude/Signature.hs:156-157).
    /// Read by [`Irreducible::prefix_ac_fct`].
    noeq_names: BTreeSet<Vec<u8>>,
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
        let mut noeq_names = BTreeSet::new();
        let mut ac_fct_syms = BTreeMap::new();
        for s in sig.fun_syms.iter() {
            match s {
                FunSym::NoEq(n) => {
                    noeq_names.insert(n.name.to_vec());
                    if n.arity == 0 {
                        nullary_names.insert(n.name.to_vec());
                    }
                }
                FunSym::Ac(AcSym::AcFct(f)) => {
                    ac_fct_syms.insert(f.name.to_vec(), *f);
                }
                _ => {}
            }
        }
        Irreducible {
            noeq,
            ac,
            ac_fct_syms,
            noeq_names,
            nullary_names,
        }
    }

    /// Is the NoEq symbol applied under `name` with `arity` arguments
    /// irreducible?  HS's guard is ``o `S.member` irreducible``
    /// (Wellformedness.hs:984) on the whole `FunSym`, so a NoEq head is
    /// matched only against NoEq members of the irreducible set, keyed by
    /// (name, arity).  A user-declared `[AC]` symbol of the same name is the
    /// distinct `FunSym` `AC (ACfct (name, _))` and cannot satisfy that test
    /// for a NoEq head; AC heads are classified by [`Self::is_ac_irreducible`]
    /// instead.  The two coexist: under `builtins: diffie-hellman` plus
    /// `functions: exp/2 [AC]`, `'a' ^ 'b'` parses as `fAppExp`
    /// (`Term/Term.hs:164`), a NoEq `exp/2` that `dhReducibleFunSig`
    /// (`Term/Term/FunctionSymbols.hs:307-308`) subtracts from the irreducible
    /// set (`Term/Maude/Signature.hs:121-124`), while the user's
    /// `AC (ACfct exp)` stays irreducible.
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

    /// The user-declared `[AC]` symbol called `name`, if the signature has one.
    fn ac_fct(&self, name: &str) -> Option<AcFctSym> {
        self.ac_fct_syms.get(name.as_bytes()).copied()
    }

    /// The AC symbol a PREFIX (or `op{a}b`) application of `name` denotes, if
    /// any.  HS `lookupArity` resolves those spellings by a list lookup over
    /// `S.toList (userDefinedFunSyms maudeSig)` in which every `NoEqUser`
    /// sorts before every `ACfctUser` (Theory/Text/Parser/Term.hs:62-72,
    /// constructor order of `UserDefinedSym`,
    /// Term/Term/FunctionSymbols.hs:146-147), so a name that is ALSO a `NoEq`
    /// symbol of the full signature resolves to that `NoEq` symbol, never the
    /// AC one.  The infix spelling bypasses `lookupArity` (`acterm`,
    /// Theory/Text/Parser/Term.hs:166-172) and keeps using [`Self::ac_fct`].
    fn prefix_ac_fct(&self, name: &str) -> Option<AcFctSym> {
        if self.noeq_names.contains(name.as_bytes()) {
            return None;
        }
        self.ac_fct(name)
    }
}

// =============================================================================
// Public entry point
// =============================================================================

/// The signature-derived state HS's `checkTerms` closes over — the
/// irreducible funsym classification (`irreducibleFunSyms maudeSig`) and the
/// arity-1 fold table.  Built once per theory; [`TermChecker::check`] runs
/// the `checkTerms` arm of HS `formulaReports` (Wellformedness.hs:999-1005,
/// see line 1003) for one annotated formula, so the combined per-formula
/// pass in [`crate::formula_reports`] can interleave it with the other two
/// arms.
pub struct TermChecker {
    irr: Irreducible,
    /// HS folds surplus args of an arity-1 function into a pair at PARSE time
    /// (`naryOpApp` `k == 1`, Theory/Text/Parser/Term.hs:94-96), so the AST the
    /// wf check inspects already carries `h(<a, b>)` (an irreducible `h/1`
    /// applied to a pair), NOT `h(a, b)`.  RS's parser performs the same fold
    /// (its `lookup_arity`-resolved `k == 1` branch parses one tuple), so on
    /// theory ASTs this fold is a no-op kept as belt-and-braces for ASTs from
    /// other producers (e.g. structural-mode parses): a unary `h(a, b)` left
    /// unfolded would resolve to a non-existent reducible `h/2` and be
    /// spuriously flagged "uses terms of the wrong form: reducible function
    /// symbols are disallowed".  (Mirrors the lemma/restriction
    /// pretty-printer in pretty_theory.rs.)
    // arity-1 no-eq function-name set; membership-only (.contains), never
    // iterated; std kept (byte-inert) — iteration order never reaches output.
    #[allow(clippy::disallowed_types)]
    arity1: std::collections::HashSet<String>,
}

impl TermChecker {
    pub fn new(sig: &MaudeSig) -> Self {
        TermChecker {
            irr: Irreducible::from_sig(sig),
            arity1: crate::elaborate::arity1_noeq_names(sig),
        }
    }

    /// The `checkTerms` finding for one annotated formula, if it has
    /// offenders.  `header` is HS's `"Lemma `n'"` / `"Restriction `n'"`.
    pub fn check(&self, header: &str, fm: &Formula) -> Option<WfError> {
        let folded = crate::elaborate::rewrite_arity1_formula(fm, &self.arity1);
        check_one(header, &folded, &self.irr).map(|msg| WfError::new("Formula terms", msg))
    }
}

/// Port of HS `formulaReports`'s `checkTerms` arm (Wellformedness.hs:999-1014, see line 1003),
/// run on its own over every lemma + restriction formula (HS `annFormulas`
/// order: all lemmas in theory order, then all restrictions).  Macros must
/// already be expanded by the caller (HS applies `applyMacroInFormula` first).
///
/// The batch / web load pipelines instead go through
/// [`crate::formula_reports::formula_reports`], which interleaves this arm
/// with the other two per formula as HS's `msum` does; this entry point
/// serves callers that want the `checkTerms` findings alone.
pub fn check_terms_wf(thy: &p::Theory, sig: &MaudeSig) -> Vec<WfError> {
    let checker = TermChecker::new(sig);
    crate::formula_reports::ann_formulas(thy)
        .into_iter()
        .filter_map(|(header, fm)| checker.check(&header, fm))
        .collect()
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
            out.push(resolve_term(tp, scope, irr));
            for arg in &fact.args {
                out.push(resolve_term(arg, scope, irr));
            }
        }
        // EqE t s -> [t, s], Subterm i j -> [i, j], Less i j -> [i, j], and
        // the multiset-`(<)` ordering relation.
        Atom::Eq(x, y) | Atom::Subterm(x, y) | Atom::Less(x, y) | Atom::LessMset(x, y) => {
            out.push(resolve_term(x, scope, irr));
            out.push(resolve_term(y, scope, irr));
        }
        // Last i -> [i]
        Atom::Last(tp) => {
            out.push(resolve_term(tp, scope, irr));
        }
        // Syntactic (predicate) atoms contribute no real terms
        // (HS `atomTerms (Syntactic _) = []`).
        Atom::Pred(_) => {}
    }
}

// =============================================================================
// Term resolution: parser AST -> RTerm (with De-Bruijn + signature lookup)
// =============================================================================

fn resolve_term(t: &Term, scope: &Scope, irr: &Irreducible) -> RTerm {
    match t {
        Term::Var(v) => resolve_var(v, scope, irr),
        Term::PubLit(s) => RTerm::PubConst(s.clone()),
        Term::FreshLit(s) => RTerm::FreshConst(s.clone()),
        Term::NatLit(s) => RTerm::NatConst(s.clone()),
        // Bare numeric/`1`/`%1` literals: HS treats these as nullary
        // irreducible Public constructors.  The DH `1` is `oneSymString =
        // "one"` and the nat `%1` is `natOneSymString = "tone"`
        // (FunctionSymbols.hs:226,236); both are arity-0 Public Constructors
        // (`oneSym`/`natOneSym`, FunctionSymbols.hs:255,267)
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
            // `op{a}b`.  HS `binaryAlgApp` (Theory/Text/Parser/Term.hs:108-121)
            // resolves the name through `lookupArity`, so a user-declared
            // `[AC]` symbol builds `fAppAC (ACfct …)` only when no `NoEq`
            // symbol shares the name ([`Irreducible::prefix_ac_fct`]);
            // otherwise `fAppNoEq`.  It has NO `em` arm, so `em{a}b` is a NoEq
            // `em/2` application, NOT the C symbol `naryOpApp` builds for the
            // prefix spelling `em(a, b)`.
            let args = vec![resolve_term(a, scope, irr), resolve_term(b, scope, irr)];
            match irr.prefix_ac_fct(name) {
                Some(f) => resolve_ac(AcSym::AcFct(f), args, irr),
                None => resolve_named(name, args, irr),
            }
        }
        Term::Pair(items) => {
            // `<a, b, c>` is right-nested `pair(a, pair(b, c))`.
            let resolved: Vec<RTerm> = items.iter().map(|i| resolve_term(i, scope, irr)).collect();
            build_pair(resolved, irr)
        }
        Term::Diff(a, b) => {
            let args = vec![resolve_term(a, scope, irr), resolve_term(b, scope, irr)];
            resolve_named("diff", args, irr)
        }
        Term::BinOp(op, a, b) => {
            let ra = resolve_term(a, scope, irr);
            let rb = resolve_term(b, scope, irr);
            match op {
                // `^` (exp) is a NoEq symbol; the rest are AC symbols.
                BinOp::Exp => resolve_named("exp", vec![ra, rb], irr),
                BinOp::Union => resolve_ac(AcSym::Union, vec![ra, rb], irr),
                BinOp::Mult => resolve_ac(AcSym::Mult, vec![ra, rb], irr),
                BinOp::Xor => resolve_ac(AcSym::Xor, vec![ra, rb], irr),
                BinOp::NatPlus => resolve_ac(AcSym::NatPlus, vec![ra, rb], irr),
                // A user-declared `[AC]` symbol applied infix is ALWAYS the
                // AC application (HS `acterm` builds `fAppACfct` straight
                // from `stACFunSyms`, Theory/Text/Parser/Term.hs:166-172) —
                // even when a `NoEq` symbol shares the name and claims the
                // prefix spelling, so this arm deliberately bypasses
                // [`Irreducible::prefix_ac_fct`]'s NoEq-wins rule.
                BinOp::AcFct(name) => match irr.ac_fct(name) {
                    Some(f) => resolve_ac(AcSym::AcFct(f), vec![ra, rb], irr),
                    None => resolve_named(name, vec![ra, rb], irr),
                },
            }
        }
        Term::PatMatch(inner) => resolve_term(inner, scope, irr),
    }
}

fn resolve_app(name: &str, args: &[Term], scope: &Scope, irr: &Irreducible) -> RTerm {
    let resolved: Vec<RTerm> = args.iter().map(|a| resolve_term(a, scope, irr)).collect();
    // HS `naryOpApp` dispatches on the WRITTEN NAME before it dispatches on
    // the signature entry: an application spelled `em(…)` becomes
    // `fAppC EMap ts` whatever `lookupArity` found — the builtin `C EMap` of
    // `bilinear-pairing`, a user `functions: em/2` declaration, even a user
    // `[AC]` declaration all take that arm
    // (HS `naryOpApp` Theory/Text/Parser/Term.hs:103).
    if name.as_bytes() == EMAP_SYM_STRING {
        return resolve_c(CSym::EMap, resolved);
    }
    if let Some(f) = irr.prefix_ac_fct(name) {
        return resolve_ac(AcSym::AcFct(f), resolved, irr);
    }
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
///
/// The node is put in AC-normal form exactly as HS `fAppAC` does
/// (Term/Term/Raw.hs:118-129): a one-argument application collapses to that
/// argument, the arguments of every direct child under the same symbol are
/// spliced into the list, and the list is sorted by [`cmp_rterm`].  Children
/// are already normal (they were built by this same function), so splicing
/// one level deep reproduces HS's fully flat argument list.
///
/// HS `fAppAC _ [] = error "Term.fAppAC: empty argument list"`; an empty node
/// is kept here instead, so a source term that upstream aborts on (a
/// user-`[AC]` symbol written with no arguments, which `naryOpApp`'s arity
/// check lets through for `IsAC` symbols) still produces a wellformedness
/// report.
fn resolve_ac(sym: AcSym, args: Vec<RTerm>, irr: &Irreducible) -> RTerm {
    let mut flat: Vec<RTerm> = Vec::with_capacity(args.len());
    for a in args {
        match a {
            RTerm::App(Head::Ac { sym: inner, .. }, inner_args) if inner == sym => {
                flat.extend(inner_args);
            }
            other => flat.push(other),
        }
    }
    if flat.len() == 1 {
        return flat.pop().expect("length checked");
    }
    flat.sort_by(cmp_rterm);
    let reducible = if matches!(sym, AcSym::Union) {
        false
    } else {
        !irr.is_ac_irreducible(sym)
    };
    RTerm::App(Head::Ac { sym, reducible }, flat)
}

/// Build a C (commutative, non-associative) application node.  HS `fAppC`
/// sorts the argument list: `fAppC nacsym as = FAPP (C nacsym) (sort as)`
/// (Term/Term/Raw.hs:132-134).
fn resolve_c(sym: CSym, mut args: Vec<RTerm>) -> RTerm {
    args.sort_by(cmp_rterm);
    RTerm::App(Head::C(sym), args)
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
fn resolve_var(v: &VarSpec, scope: &Scope, irr: &Irreducible) -> RTerm {
    if let Some(idx) = lookup_bound(v, scope) {
        return RTerm::Bound(idx);
    }
    // Not bound: a bare message-sorted name that is a declared nullary funsym
    // is an application (e.g. private `f/0` parsed as Var("f")).
    if v.sort == SortHint::Msg && irr.nullary_named(&v.name) {
        return resolve_named(&v.name, vec![], irr);
    }
    RTerm::Free(v.clone())
}

/// Find the innermost binder matching `v` and return its De-Bruijn index.
///
/// HS binds a use to its binder via full `LVar` equality — name AND sort AND
/// idx (`quantify x = ... | v == x = Bound i`, Theory/Model/Formula.hs:347-352; `LVar` `Eq`
/// compares `idx`, sort and name, LTerm.hs:546-548). We reproduce this on the
/// sort-*kind*, over the concrete `LSort` the parser gave each occurrence
/// (Theory/Text/Parser/Formula.hs:112-117, see line 114
/// `standardFormula msgvar nodevar`): a message-position variable comes from
/// `msgvar`, whose bare arm is `LSortMsg` (Token.hs:424-426, 440-441), and a
/// temporal-position one from `nodevar` (`LSortNode`, Token.hs:444-447).
///
/// `quantify`'s `v == x` then compares sort exactly, so a bare `x` binds
/// only to a `LSortMsg` binder, never to a `~x`/`$x`/`%x`/`#x` binder of the
/// same name+idx. The `idx` comparison likewise keeps `x.1` and `x.2` distinct.
fn lookup_bound(v: &VarSpec, scope: &Scope) -> Option<u32> {
    let expected: u8 = kind_of(&v.sort);
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
        // `C EMap` is never irreducible (see `Head::C`), so it falls through
        // to HS's catch-all `allowed _ = False` whatever its arguments are.
        RTerm::App(Head::C(_), _) => false,
        // Free vars, fresh/nat name constants -> offenders.
        RTerm::Free(_) | RTerm::FreshConst(_) | RTerm::NatConst(_) => false,
    }
}

// =============================================================================
// Term ordering (HS derived `Ord (Term (Lit Name (BVar LVar)))`)
// =============================================================================

/// `Ord` on the terms HS sorts inside `fAppAC` / `fAppC`, restricted to the
/// shapes an [`RTerm`] can take.
///
/// `Term a = LIT a | FAPP FunSym [Term a]` derives `Ord`
/// (Term/Term/Raw.hs:72-74), so every `LIT` precedes every `FAPP`; two
/// `FAPP`s compare their `FunSym` (see [`funsym_key`]) and then their
/// argument lists positionally.  Inside `LIT`, `Lit c v = Con c | Var v`
/// derives `Con < Var` (VTerm.hs:56-57); a `Con` is a `Name` compared by its
/// `NameTag` (`FreshName | PubName | NodeName | NatName | AbbrevName`,
/// LTerm.hs:219-220) and then by its `NameId` string; a `Var` is a
/// `BVar LVar` with `Bound < Free` (LTerm.hs:476-478), `Bound` by index and
/// `Free` by the `LVar` order `(idx, sort, name)` (LTerm.hs:546-548).
fn cmp_rterm(a: &RTerm, b: &RTerm) -> std::cmp::Ordering {
    match (a, b) {
        (RTerm::App(ha, xs), RTerm::App(hb, ys)) => funsym_key(ha, xs.len())
            .cmp(&funsym_key(hb, ys.len()))
            .then_with(|| crate::guarded::cmp_slice(xs, ys, cmp_rterm)),
        (RTerm::Bound(m), RTerm::Bound(n)) => m.cmp(n),
        (RTerm::Free(v), RTerm::Free(w)) => crate::guarded::cmp_varspec(v, w),
        (RTerm::FreshConst(m), RTerm::FreshConst(n))
        | (RTerm::PubConst(m), RTerm::PubConst(n))
        | (RTerm::NatConst(m), RTerm::NatConst(n)) => m.cmp(n),
        // Different constructors: the tag alone decides.
        _ => rterm_tag(a).cmp(&rterm_tag(b)),
    }
}

/// Constructor rank of an [`RTerm`]: the three name constants in `NameTag`
/// order, then `Bound`, then `Free` (all still `LIT`), then every `FAPP`.
fn rterm_tag(t: &RTerm) -> u8 {
    match t {
        RTerm::FreshConst(_) => 0,
        RTerm::PubConst(_) => 1,
        RTerm::NatConst(_) => 2,
        RTerm::Bound(_) => 3,
        RTerm::Free(_) => 4,
        RTerm::App(..) => 5,
    }
}

/// HS `Ord FunSym` key for an application head: `(outer, name, k)`.
///
/// `outer` is the `FunSym` constructor order `NoEq(0) < AC(1) < C(2)`
/// (List(3) has no `RTerm` spelling; FunctionSymbols.hs:150-154).  For a
/// `NoEq` symbol `(name, k)` is `Ord NoEqSym`'s leading `(name, arity)` —
/// privacy/constructability/NDC never disambiguate two symbols that share a
/// name, since HS's `lookupArity` keys the whole declaration table on the
/// name (Theory/Text/Parser/Term.hs:62-67).  The builtin AC ops carry no
/// name, so their `ACSym` order `Union < Mult < Xor < NatPlus < ACfct`
/// (FunctionSymbols.hs:138-139) rides in `k`, and their empty name keeps
/// them ahead of every user `ACfct` — whose own name orders two `ACfct`s,
/// mirroring `Ord ACfctSym`.  `CSym` is a single nullary constructor, so
/// every `C` head ties on `name` and `k`.
fn funsym_key(head: &Head, arity: usize) -> (u8, &[u8], usize) {
    match head {
        Head::App { name, .. } => (0, name.as_bytes(), arity),
        Head::Ac { sym, .. } => match sym {
            AcSym::Union => (1, b"", 0),
            AcSym::Mult => (1, b"", 1),
            AcSym::Xor => (1, b"", 2),
            AcSym::NatPlus => (1, b"", 3),
            AcSym::AcFct(f) => (1, f.name, 4),
        },
        Head::C(CSym::EMap) => (2, b"", 0),
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
            // HS `Show (Term a)` (Term/Raw.hs):
            //   FApp (NoEq (s,_)) [] -> s
            //   FApp (NoEq (s,_)) as -> s ++ "(" ++ intercalate "," ... ++ ")"
            //   FApp (AC (ACfct (s,_))) as -> s ++ "(" ++ ... ++ ")"
            //   FApp (C EMap) as     -> "em" ++ "(" ++ ... ++ ")"
            //   FApp (AC o) as       -> show o ++ "(" ++ ... ++ ")"
            // ACSym derives Show as the constructor name (Union/Mult/Xor/NatPlus);
            // user-defined AC symbols print their own name.
            let name: std::borrow::Cow<'_, str> = match head {
                Head::App { name, .. } => name.as_str().into(),
                Head::Ac { sym, .. } => match sym {
                    AcSym::Union => "Union".into(),
                    AcSym::Mult => "Mult".into(),
                    AcSym::Xor => "Xor".into(),
                    AcSym::NatPlus => "NatPlus".into(),
                    AcSym::AcFct(s) => String::from_utf8_lossy(s.name),
                },
                Head::C(CSym::EMap) => String::from_utf8_lossy(EMAP_SYM_STRING),
            };
            out.push_str(&name);
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
    fn bare_message_use_does_not_bind_to_node_binder() {
        // A bare message-position use `x` must NOT bind to a `#x` node
        // binder of the same name+idx: HS's `LVar` Eq compares sort, and the
        // parser gives a bare message use the concrete sort `LSortMsg`,
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
            "bare use must stay Free (not bind to #x), got:\n{}",
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

    /// The one offender rendering of the single block `report` produced.
    fn one_offender(report: &[WfError], want: &str) {
        assert_eq!(report.len(), 1, "expected one block, got {:?}", report);
        assert!(
            report[0].message.contains(want),
            "expected offender {}, got:\n{}",
            want,
            report[0].message
        );
    }

    #[test]
    fn prefix_em_is_a_reducible_c_symbol_even_when_user_declared() {
        // `functions: em/2` with NO `bilinear-pairing`: HS's `naryOpApp`
        // still routes the prefix spelling `em(…)` to `fAppC EMap`
        // (Theory/Text/Parser/Term.hs:103), and `C EMap` is not in the
        // signature at all here — so the enclosing `*` is an offender even
        // though `f/2`, `em/2` and `AC Mult` all look irreducible by name.
        //
        // Oracle bytes (ef3f0468, div2/user_em2.spthy):
        //   Lemma `L1' uses terms of the wrong form:
        //     `Mult(f('g','h'),em('g','h'))'
        let src = "theory T begin\n\
                   builtins: diffie-hellman\n\
                   functions: em/2, f/2\n\
                   lemma L1:\n  \"All #i. Test(em('g', 'h') * f('g', 'h')) @ #i ==> F\"\n\
                   end\n";
        let (thy, sig) = sig_of(src);
        one_offender(
            &check_terms_wf(&thy, &sig),
            "`Mult(f('g','h'),em('g','h'))'",
        );
    }

    #[test]
    fn em_written_as_alg_app_stays_a_noeq_symbol() {
        // `em{a}b` goes through `binaryAlgApp`, which has no `em` arm and
        // builds `fAppNoEq ("em", …)` (Theory/Text/Parser/Term.hs:108-121).
        // So it sorts among the NoEq symbols ("em" < "f") instead of after
        // them, unlike the prefix spelling above.
        //
        // Oracle bytes (ef3f0468, div2/algapp_em.spthy):
        //   `Mult(em('g','h'),f('g','h'))'
        let src = "theory T begin\n\
                   builtins: bilinear-pairing\n\
                   functions: f/2\n\
                   lemma L1:\n  \"All #i. Test(em{'g'}'h' * f('g', 'h')) @ #i ==> F\"\n\
                   end\n";
        let (thy, sig) = sig_of(src);
        one_offender(
            &check_terms_wf(&thy, &sig),
            "`Mult(em('g','h'),f('g','h'))'",
        );
    }

    #[test]
    fn c_and_ac_arguments_sort_on_the_de_bruijn_form() {
        // `em(x, y)` sorts its two arguments AFTER `quantify` has replaced
        // them by De Bruijn indices, so the pair comes out ascending in the
        // INDEX (`Bound 1` before `Bound 2`) — the reverse of the source
        // order, in which `x` precedes `y`.  The enclosing `Mult` sorts its
        // NoEq operand ahead of the C operand.
        //
        // Oracle bytes (ef3f0468, div2/em_c_tier.spthy lemma L2):
        //     `Mult(aaa(Bound 2,Bound 1),em(Bound 1,Bound 2))',
        //     `Mult(f(Bound 3,Bound 2),em(Bound 2,Bound 3))'
        let src = "theory T begin\n\
                   builtins: bilinear-pairing\n\
                   functions: f/2, aaa/2\n\
                   lemma L2:\n  \"All x y #i. Test2(em(x, y) * aaa(x, y)) @ #i ==> \
                     Ex #j. Test(em(x, y) * f(x, y)) @ #j\"\n\
                   end\n";
        let (thy, sig) = sig_of(src);
        let report = check_terms_wf(&thy, &sig);
        assert_eq!(report.len(), 1, "expected one block, got {:?}", report);
        assert!(
            report[0].message.contains(
                "`Mult(aaa(Bound 2,Bound 1),em(Bound 1,Bound 2))',\n    \
                 `Mult(f(Bound 3,Bound 2),em(Bound 2,Bound 3))'"
            ),
            "got:\n{}",
            report[0].message
        );
    }

    #[test]
    fn builtin_ac_arguments_are_flattened_and_sorted() {
        // `('b' ++ 'a') ++ ('c' XOR 'd')`: `fAppAC` splices the nested
        // `Union` node's arguments into the outer one and sorts the result,
        // so the two constants precede the `Xor` application.
        //
        // Oracle bytes (ef3f0468):
        //   `Union('a','b',Xor('c','d'))'
        let src = "theory T begin\n\
                   builtins: xor, multiset\n\
                   lemma L3:\n  \"All #i. Test(('b' ++ 'a') ++ ('c' XOR 'd')) @ #i ==> F\"\n\
                   end\n";
        let (thy, sig) = sig_of(src);
        one_offender(&check_terms_wf(&thy, &sig), "`Union('a','b',Xor('c','d'))'");
    }

    #[test]
    fn user_ac_symbol_written_prefix_is_flattened_and_sorted() {
        // A `[AC]` symbol applied prefix is `fAppAC (ACfct …)` whatever the
        // written arity (Theory/Text/Parser/Term.hs:104-105), so the nested
        // `uac('z','a')` is spliced in and the whole list sorted.
        //
        // Oracle bytes (ef3f0468):
        //   Lemma `L1' ... `uac('a',red('b','a'))'
        //   Lemma `L2' ... `uac('a','z',red('b','c'))'
        let src = "theory T begin\n\
                   functions: uac/2 [AC], red/2\n\
                   equations: red(x, y) = x\n\
                   lemma L1:\n  \"All #i. Test(uac(red('b','a'), 'a')) @ #i ==> F\"\n\
                   lemma L2:\n  \"All #i. Test(uac(uac('z','a'), red('b','c'))) @ #i ==> F\"\n\
                   end\n";
        let (thy, sig) = sig_of(src);
        let report = check_terms_wf(&thy, &sig);
        assert_eq!(report.len(), 2, "expected two blocks, got {:?}", report);
        assert!(
            report[0].message.contains("`uac('a',red('b','a'))'"),
            "got:\n{}",
            report[0].message
        );
        assert!(
            report[1].message.contains("`uac('a','z',red('b','c'))'"),
            "got:\n{}",
            report[1].message
        );
    }

    #[test]
    fn bare_free_variable_under_at_keeps_its_node_sort() {
        // `@ i` is parsed by `nodevar`, so the free `i` is an `LSortNode`
        // `LVar` and `Show LVar` prefixes it with `#`.
        //
        // Oracle bytes (ef3f0468): `Free #i'
        let src = "theory T begin\n\
                   lemma L1:\n  \"All #j. K('c') @ i ==> F\"\n\
                   end\n";
        let (thy, sig) = sig_of(src);
        one_offender(&check_terms_wf(&thy, &sig), "`Free #i'");
    }
}
