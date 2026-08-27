// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Term.Maude.Signature` from
//! `lib/term/src/Term/Maude/Signature.hs`.
//!
//! `MaudeSig` describes the equational theory the prover is configured
//! with — which built-in AC operators are enabled (DH, BP, MSet, Nat,
//! XOR), plus user-supplied subterm rules.

use std::collections::BTreeSet;

use crate::builtin::{
    asym_enc_dest_rules, asym_enc_fun_dest_sig, asym_enc_fun_sig, asym_enc_rules, bp_rules,
    dh_rules, fst_dest_rule, fst_rule, hash_fun_sig, location_report_fun_sig,
    location_report_rules, mset_rules, pair_dest_rules, pair_rules, reveal_signature_fun_sig,
    reveal_signature_rules, signature_dest_rules, signature_fun_dest_sig, signature_fun_sig,
    signature_rules, snd_dest_rule, snd_rule, sym_enc_dest_rules, sym_enc_fun_dest_sig,
    sym_enc_fun_sig, sym_enc_rules, xor_rules,
};
use crate::function_symbols::{
    bp_fun_sig, bp_reducible_fun_sig, dh_fun_sig, dh_reducible_fun_sig, fst_dest_sym, fst_sym,
    mset_fun_sig, nat_fun_sig, pair_fun_dest_sig, pair_fun_sig, snd_dest_sym, snd_sym, xor_fun_sig,
    xor_reducible_fun_sig, AcFctFunSig, AcFctSym, AcSym, Constructability, FunSig, FunSym,
    NdcState, NoEqFunSig, NoEqSym, Privacy, UserDefinedSig, UserDefinedSym,
};
use crate::lterm::LNTerm;
use crate::rewriting::RRule;
use crate::subterm_rule::CtxtStRule;
use crate::term::Term;

/// HS `stRules :: S.Set CtxtStRule` (Term/Maude/Signature.hs:99), paired with the
/// `maude_proc::term_ac_c_free` verdict of each rule's LHS.
///
/// `norm::go_nf` needs that verdict per rule — at every `App` node of every
/// normal-form check — to choose between the pure no-AC st-rule matcher and
/// the Maude-backed one, and computing it walks the whole LHS, so it is held
/// rather than recomputed.  Both fields are private and are rebuilt together
/// by every mutator, so a flag can never describe a rule other than the one it
/// is read alongside; the pairing is only observable through
/// [`StRules::iter_with_lhs_ac_c_free`], which zips the two.
///
/// Reading is otherwise the `BTreeSet`'s own API, via `Deref` — including the
/// `S.toList` iteration order that reaches the emitted Maude text, the
/// `equations:` pretty-print and the wellformedness report.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct StRules {
    rules: BTreeSet<CtxtStRule>,
    lhs_ac_c_free: Vec<bool>,
}

impl StRules {
    /// Each rule together with the Ac/C-freeness of its LHS, in `BTreeSet`
    /// iteration order.
    pub fn iter_with_lhs_ac_c_free(&self) -> impl Iterator<Item = (&CtxtStRule, bool)> + '_ {
        self.rules.iter().zip(self.lhs_ac_c_free.iter().copied())
    }

    /// True iff EVERY rule LHS is Ac/C-free.
    pub fn all_lhs_ac_c_free(&self) -> bool {
        self.lhs_ac_c_free.iter().all(|&b| b)
    }

    /// `BTreeSet::insert`, re-deriving the LHS flags.
    pub fn insert(&mut self, rule: CtxtStRule) -> bool {
        let added = self.rules.insert(rule);
        if added {
            self.derive_lhs_ac_c_free();
        }
        added
    }

    /// `BTreeSet::remove`, re-deriving the LHS flags.
    pub fn remove(&mut self, rule: &CtxtStRule) -> bool {
        let removed = self.rules.remove(rule);
        if removed {
            self.derive_lhs_ac_c_free();
        }
        removed
    }

    fn derive_lhs_ac_c_free(&mut self) {
        self.lhs_ac_c_free = self
            .rules
            .iter()
            .map(|r| crate::maude_proc::term_ac_c_free(&r.lhs))
            .collect();
    }
}

impl std::ops::Deref for StRules {
    type Target = BTreeSet<CtxtStRule>;
    fn deref(&self) -> &Self::Target {
        &self.rules
    }
}

impl<'a> IntoIterator for &'a StRules {
    type Item = &'a CtxtStRule;
    type IntoIter = std::collections::btree_set::Iter<'a, CtxtStRule>;
    fn into_iter(self) -> Self::IntoIter {
        self.rules.iter()
    }
}

impl From<BTreeSet<CtxtStRule>> for StRules {
    fn from(rules: BTreeSet<CtxtStRule>) -> Self {
        let mut s = StRules {
            rules,
            lhs_ac_c_free: Vec::new(),
        };
        s.derive_lhs_ac_c_free();
        s
    }
}

impl FromIterator<CtxtStRule> for StRules {
    fn from_iter<I: IntoIterator<Item = CtxtStRule>>(iter: I) -> Self {
        Self::from(iter.into_iter().collect::<BTreeSet<CtxtStRule>>())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct MaudeSig {
    pub enable_dh: bool,
    pub enable_bp: bool,
    pub enable_mset: bool,
    pub enable_nat: bool,
    pub enable_xor: bool,
    pub enable_diff: bool,
    pub st_fun_syms: BTreeSet<NoEqSym>,
    /// User-defined AC function signature (HS `stACFunSyms`).  These are the
    /// symbols declared `[AC]` in the theory's `functions:` block; the
    /// built-in AC operators live in the `enable_*` flags instead.
    pub st_ac_fun_syms: BTreeSet<AcFctSym>,
    /// The subterm rewrite rules, each carrying the Ac/C-freeness of its LHS
    /// (see [`StRules`]).
    pub st_rules: StRules,
    pub macro_names: BTreeSet<NoEqSym>,
    pub eq_convergent: bool,
    pub fun_syms: FunSig,
    pub irreducible_fun_syms: FunSig,
    pub reducible_fun_syms: FunSig,
    /// Hash-set mirrors of `irreducible_fun_syms` / `reducible_fun_syms`, kept
    /// in lock-step by [`MaudeSig::refresh`].  The proof search's hottest
    /// predicates (`elem_not_below_reducible`, `any_non_nf`,
    /// `maybe_not_nf_subterms`) probe membership per term node, recursively;
    /// these give O(1) `contains` instead of the `BTreeSet`'s O(log n)
    /// `FunSym::cmp` tree-walk.  The `BTreeSet`s are retained because their
    /// SORTED iteration order reaches rendered output (signature pretty-print,
    /// wellformedness) — only the boolean membership tests use these mirrors,
    /// so the two are membership-identical and the output is unchanged.
    pub irreducible_fun_syms_fast: tamarin_utils::FastSet<FunSym>,
    pub reducible_fun_syms_fast: tamarin_utils::FastSet<FunSym>,
    /// The symbol a NAME resolves to, in the order HS `lookupArity` searches
    /// (Theory/Text/Parser/Term.hs:62-72): the free symbols of `fun_syms`,
    /// then its user-defined AC symbols (together HS `userDefinedFunSyms`,
    /// Term/Maude/Signature.hs:162-164), then `macro_names`.  The first entry
    /// of that order wins, and the built-in AC/C/`List` symbols — which carry
    /// no name and are not part of `userDefinedFunSyms` — are absent.  Filled
    /// by [`MaudeSig::refresh`] and read through [`MaudeSig::fun_sym_named`].
    ///
    /// [`MaudeSig::user_defined_fun_syms`] answers the same question by
    /// building two `BTreeSet`s per call; a lookup here allocates nothing.
    pub fun_syms_by_name: tamarin_utils::FastMap<&'static [u8], FunSym>,
}

impl MaudeSig {
    /// True when the signature declares NO associative-commutative operators
    /// (DH / BP / multiset / nat / XOR, or a user-defined `[AC]` symbol).  The
    /// local Robinson unifier and the `reduce` identity fast-path are complete
    /// only for such signatures; this is the single source of truth for that
    /// "no AC theory" predicate.
    pub fn has_no_ac_operators(&self) -> bool {
        !self.enable_dh
            && !self.enable_bp
            && !self.enable_mset
            && !self.enable_nat
            && !self.enable_xor
            && self.st_ac_fun_syms.is_empty()
    }

    /// True iff EVERY `st_rules` LHS is Ac/C-free, i.e. the no-AC st-rule
    /// matcher of `norm::nf_via_haskell` is complete for this signature.
    pub fn st_lhs_all_ac_c_free(&self) -> bool {
        self.st_rules.all_lhs_ac_c_free()
    }

    /// HS `maudeSig` (Term/Maude/Signature.hs:110-125#maudeSig): recompute the
    /// cached `fun_syms` / `irreducible_fun_syms` / `reducible_fun_syms` from
    /// the source-of-truth flags.
    pub fn refresh(mut self) -> Self {
        if self.enable_bp {
            self.enable_dh = true;
        }
        let mut all_funs: FunSig = self.st_fun_syms.iter().map(|s| FunSym::NoEq(*s)).collect();
        if self.enable_dh || self.enable_bp {
            all_funs.extend(dh_fun_sig());
        }
        if self.enable_bp {
            all_funs.extend(bp_fun_sig());
        }
        if self.enable_mset {
            all_funs.extend(mset_fun_sig());
        }
        if self.enable_nat {
            all_funs.extend(nat_fun_sig());
        }
        if self.enable_xor {
            all_funs.extend(xor_fun_sig());
        }
        all_funs.extend(
            self.st_ac_fun_syms
                .iter()
                .map(|s| FunSym::Ac(AcSym::AcFct(*s))),
        );

        // Reducible roots: any function symbol at the root of an stRules LHS,
        // plus DH/BP/XOR reducible. AC Mult is intentionally absent.
        let mut reducible_without_mult: FunSig = BTreeSet::new();
        for r in &self.st_rules {
            if let Term::App(o, _) = &r.lhs {
                reducible_without_mult.insert(*o);
            }
        }
        reducible_without_mult.extend(dh_reducible_fun_sig());
        reducible_without_mult.extend(bp_reducible_fun_sig());
        reducible_without_mult.extend(xor_reducible_fun_sig());

        let irreducible: FunSig = all_funs
            .difference(&reducible_without_mult)
            .copied()
            .collect();

        let mut reducible: FunSig = BTreeSet::new();
        for r in self.rrules() {
            if let Term::App(o, _) = &r.lhs {
                reducible.insert(*o);
            }
        }

        // Hash-set mirrors for O(1) membership in the proof-search hot path.
        // Kept in lock-step with the BTreeSets above (same elements), so every
        // `.contains()` answer is identical — only the cost differs.
        self.irreducible_fun_syms_fast = irreducible.iter().copied().collect();
        self.reducible_fun_syms_fast = reducible.iter().copied().collect();

        // Name index, in the order HS `lookupArity` (Theory/Text/Parser/Term.hs:62-72)
        // searches: `userDefinedFunSyms` — the free symbols of `fun_syms`
        // before its user-defined AC ones, each half in the symbol's own order
        // — then the macro names.  HS `lookup` takes the first match, so an
        // entry already in the map is never overwritten.
        let mut by_name: tamarin_utils::FastMap<&'static [u8], FunSym> =
            tamarin_utils::FastMap::default();
        for sym in all_funs
            .iter()
            .copied()
            .chain(self.macro_names.iter().copied().map(FunSym::NoEq))
        {
            if let Some(name) = user_defined_name(sym) {
                by_name.entry(name).or_insert(sym);
            }
        }
        self.fun_syms_by_name = by_name;
        self.fun_syms = all_funs;
        self.irreducible_fun_syms = irreducible;
        self.reducible_fun_syms = reducible;
        self
    }

    /// `rrulesForMaudeSig`: every rewrite rule active for this signature.
    pub fn rrules(&self) -> BTreeSet<RRule<LNTerm>> {
        let mut s: BTreeSet<RRule<LNTerm>> = self.st_rules.iter().map(|r| r.to_rrule()).collect();
        if self.enable_dh {
            s.extend(dh_rules());
        }
        if self.enable_bp {
            s.extend(bp_rules());
        }
        if self.enable_mset {
            s.extend(mset_rules());
        }
        if self.enable_xor {
            s.extend(xor_rules());
        }
        s
    }

    pub fn no_eq_fun_syms(&self) -> NoEqFunSig {
        self.fun_syms
            .iter()
            .filter_map(|f| {
                if let FunSym::NoEq(s) = f {
                    Some(*s)
                } else {
                    None
                }
            })
            .collect()
    }

    /// AC function symbols in the signature (HS `acUserFunSyms`), read back out
    /// of the derived `fun_syms` rather than `st_ac_fun_syms`.
    pub fn ac_user_fun_syms(&self) -> AcFctFunSig {
        self.fun_syms
            .iter()
            .filter_map(|f| {
                if let FunSym::Ac(AcSym::AcFct(s)) = f {
                    Some(*s)
                } else {
                    None
                }
            })
            .collect()
    }

    /// The symbol HS `lookupArity` (Theory/Text/Parser/Term.hs:62-72) resolves
    /// `name` to, or `None` where HS fails with `unknown operator`: the first
    /// entry of `userDefinedFunSyms` (Term/Maude/Signature.hs:162-164) —
    /// free symbols before user-defined AC symbols — and then of the macro
    /// names.  HS's association list ends in a hard-coded `em/2` row that
    /// belongs to no signature, so `em` is answered here only when the
    /// signature itself declares it.
    pub fn fun_sym_named(&self, name: &[u8]) -> Option<FunSym> {
        self.fun_syms_by_name.get(name).copied()
    }

    /// The user-defined AC symbol of this name, read off `fun_syms` like HS
    /// `acUserFunSyms` (Term/Maude/Signature.hs:160-161).
    /// [`MaudeSig::fun_sym_named`] answers with the free symbol when one
    /// shares the name, so a question about the AC symbol alone asks here.
    pub fn ac_fct_sym_named(&self, name: &[u8]) -> Option<AcFctSym> {
        self.fun_syms.iter().find_map(|f| match f {
            FunSym::Ac(AcSym::AcFct(s)) if s.name == name => Some(*s),
            _ => None,
        })
    }

    /// HS `userDefinedFunSyms`: every free symbol of the signature plus every
    /// user-defined AC symbol, tagged with which kind it is.
    ///
    /// Intentionally retained: faithful mirror of HS `userDefinedFunSyms`
    /// (Term/Maude/Signature.hs:163-164).  No call site in the port — HS calls
    /// it from the parser (Theory/Text/Parser/Macro.hs:43,
    /// Theory/Text/Parser/Term.hs:65), whereas the port answers the same
    /// question through [`MaudeSig::fun_syms_by_name`], which allocates
    /// nothing.  [`MaudeSig::user_defined_st_fun_syms`] is the variant
    /// intruder-rule generation uses.
    pub fn user_defined_fun_syms(&self) -> UserDefinedSig {
        self.no_eq_fun_syms()
            .into_iter()
            .map(UserDefinedSym::NoEqUser)
            .chain(
                self.ac_user_fun_syms()
                    .into_iter()
                    .map(UserDefinedSym::AcFctUser),
            )
            .collect()
    }

    /// HS `userDefinedSTFunSyms`: like [`MaudeSig::user_defined_fun_syms`], but
    /// the free part is the SUBTERM-theory signature (`st_fun_syms`), i.e. it
    /// excludes the symbols contributed by the built-in theories.
    pub fn user_defined_st_fun_syms(&self) -> UserDefinedSig {
        self.st_fun_syms
            .iter()
            .copied()
            .map(UserDefinedSym::NoEqUser)
            .chain(
                self.ac_user_fun_syms()
                    .into_iter()
                    .map(UserDefinedSym::AcFctUser),
            )
            .collect()
    }

    /// Add a user-defined function symbol: free symbols go to `st_fun_syms`,
    /// AC symbols to `st_ac_fun_syms`.
    ///
    /// HS `addFunSym funsym msig = msig <> mempty {stFunSyms = [funsym]}`
    /// (Term/Maude/Signature.hs:170-173) — the `<>` routes through
    /// `unionExceptPairSym`, so adding the `fst`/`snd` DESTRUCTOR variant
    /// removes the built-in CONSTRUCTOR variant (and vice versa).  A plain
    /// `insert` would leave BOTH `fst/1` and `fst/1[destructor]` in the set,
    /// printing the symbol twice in the `functions:` header.  The AC branch has
    /// no such exception: HS `<>` unions `stACFunSyms` plainly.
    pub fn add_fun_sym(mut self, sym: UserDefinedSym) -> Self {
        match sym {
            UserDefinedSym::NoEqUser(f) => {
                self.st_fun_syms = union_except_pair_sym(&self.st_fun_syms, &BTreeSet::from([f]));
            }
            UserDefinedSym::AcFctUser(f) => {
                self.st_ac_fun_syms.insert(f);
            }
        }
        // HS `<>` (Term/Maude/Signature.hs:128-150) rebuilds via
        // `maudeSig (mempty {...})`, and `mempty` has `eqConvergent=False`
        // (line 153), which `maudeSig` preserves (line 112).  So routing through
        // the monoid RESETS eqConvergent to false; mirror that here.
        self.eq_convergent = false;
        self.refresh()
    }

    /// Join `ndc_state` onto the NDC state of every symbol in the subterm
    /// signature whose NAME matches `fun_sym`'s.
    ///
    /// HS `joinNDCinSig` (Term/Maude/Signature.hs:233-247) matches by name only, because
    /// the NDC state of the symbol handed in may differ from the one recorded
    /// in the signature (e.g. for symbols read out of the metadata of
    /// diff-mode intruder rules).  `fun_sym`s that carry no name (the built-in
    /// AC/C operators, `List`) match nothing.
    ///
    /// Note that HS updates the two subterm-signature sets with a record
    /// update and does NOT re-run `maudeSig`, so the derived `fun_syms` /
    /// irreducible / reducible caches keep the pre-join NDC states — no
    /// `refresh()` here either.
    pub fn join_ndc_in_sig(mut self, fun_sym: FunSym, ndc_state: NdcState) -> Self {
        let Some(name) = user_defined_name(fun_sym) else {
            return self;
        };
        self.st_fun_syms = self
            .st_fun_syms
            .iter()
            .map(|s| {
                if s.name == name {
                    s.with_ndc(ndc_state.join(s.ndc))
                } else {
                    *s
                }
            })
            .collect();
        self.st_ac_fun_syms = self
            .st_ac_fun_syms
            .iter()
            .map(|s| {
                if s.name == name {
                    s.with_ndc(ndc_state.join(s.ndc))
                } else {
                    *s
                }
            })
            .collect();
        self
    }

    /// The `functions:` list of HS `prettyMaudeSigExcept`
    /// (Term/Maude/Signature.hs:252-295): the subterm signature's free symbols rendered
    /// as `name/arity[attrs]`, followed by the user-defined AC symbols as
    /// `name/2[attrs]`, both skipping the entries listed in `excl`.
    ///
    /// The two attribute lists differ: a PRIVATE CONSTRUCTOR free symbol
    /// prints `[private,constructor]` while its AC counterpart prints just
    /// `[private]` (the `AC` attribute already implies constructability).
    pub fn pretty_fun_syms_except(&self, excl: &UserDefinedSig) -> Vec<String> {
        let mut out: Vec<String> = Vec::new();
        for sym in &self.st_fun_syms {
            if excl.contains(&UserDefinedSym::NoEqUser(*sym)) {
                continue;
            }
            let mut attrs: Vec<&str> = match (sym.privacy, sym.constructability) {
                (Privacy::Public, Constructability::Destructor) => vec!["destructor"],
                (Privacy::Private, Constructability::Destructor) => vec!["private", "destructor"],
                (Privacy::Private, Constructability::Constructor) => vec!["private", "constructor"],
                (Privacy::Public, Constructability::Constructor) => vec![],
            };
            attrs.extend(ndc_attrs(sym.ndc));
            out.push(format!(
                "{}/{}{}",
                String::from_utf8_lossy(sym.name),
                sym.arity,
                show_attrs(&attrs)
            ));
        }
        for sym in &self.st_ac_fun_syms {
            if excl.contains(&UserDefinedSym::AcFctUser(*sym)) {
                continue;
            }
            let mut attrs: Vec<&str> = match (sym.privacy, sym.constructability) {
                (Privacy::Public, Constructability::Destructor) => vec!["destructor"],
                (Privacy::Private, Constructability::Destructor) => vec!["private", "destructor"],
                (Privacy::Private, Constructability::Constructor) => vec!["private"],
                (Privacy::Public, Constructability::Constructor) => vec![],
            };
            attrs.push("AC");
            attrs.extend(ndc_attrs(sym.ndc));
            out.push(format!(
                "{}/2{}",
                String::from_utf8_lossy(sym.name),
                show_attrs(&attrs)
            ));
        }
        out
    }

    /// Add a macro symbol.
    ///
    /// HS `addMacroSym funsym msig = msig <> mempty {macroNames=...}`
    /// (Term/Maude/Signature.hs:176-178) routes through the monoid `<>`, which
    /// rebuilds from `mempty` (eqConvergent=False, line 153; preserved by
    /// `maudeSig`, line 112) and so RESETS eqConvergent to false — match that.
    pub fn add_macro_sym(mut self, sym: NoEqSym) -> Self {
        self.macro_names.insert(sym);
        self.eq_convergent = false;
        self.refresh()
    }

    /// Add a context subterm rule.
    pub fn add_ctxt_st_rule(mut self, rule: CtxtStRule) -> Self {
        // HS-faithful pair mutual-exclusion (`unionExceptPairRules`,
        // Term/Maude/Signature.hs:144): the fst/snd CONSTRUCTOR and
        // DESTRUCTOR rule variants are mutually exclusive.  HS `addCtxtStRule`
        // (Term/Maude/Signature.hs:181-183) is `msig <> mempty {stRules=[str]}`,
        // so each user `equations:` rule goes through the monoid `<>`, which
        // applies `unionExceptPairRules` (Term/Maude/Signature.hs:128-150, see
        // line 139) — it is NOT a plain
        // set insert.  So an exported theory that declares `fst/1[destructor]` +
        // the pairing equation must keep only the declared destructor rule, not
        // BOTH the base constructor rule AND the user destructor rule (which
        // would render the equation twice, e.g. noise/secrecy_4_passiveINpsk1_proof).
        // Mirror HS here: inserting a pair destructor rule drops the constructor
        // variant and vice versa, matching the declared symbol.
        if rule == fst_dest_rule() {
            self.st_rules.remove(&fst_rule());
        } else if rule == fst_rule() {
            self.st_rules.remove(&fst_dest_rule());
        } else if rule == snd_dest_rule() {
            self.st_rules.remove(&snd_rule());
        } else if rule == snd_rule() {
            self.st_rules.remove(&snd_dest_rule());
        }
        self.st_rules.insert(rule);
        self.refresh()
    }

    pub fn merge(self, other: Self) -> Self {
        let merged = MaudeSig {
            enable_dh: self.enable_dh || other.enable_dh,
            enable_bp: self.enable_bp || other.enable_bp,
            enable_mset: self.enable_mset || other.enable_mset,
            enable_nat: self.enable_nat || other.enable_nat,
            enable_xor: self.enable_xor || other.enable_xor,
            enable_diff: self.enable_diff || other.enable_diff,
            st_fun_syms: union_except_pair_sym(&self.st_fun_syms, &other.st_fun_syms),
            // HS `<>` unions `stACFunSyms` plainly (Term/Maude/Signature.hs:138): the
            // `fst`/`snd` constructor-vs-destructor exception applies to the
            // free symbols only.
            st_ac_fun_syms: self
                .st_ac_fun_syms
                .union(&other.st_ac_fun_syms)
                .copied()
                .collect(),
            st_rules: union_except_pair_rules(&self.st_rules, &other.st_rules).into(),
            macro_names: self
                .macro_names
                .union(&other.macro_names)
                .copied()
                .collect(),
            eq_convergent: false,
            fun_syms: BTreeSet::new(),
            irreducible_fun_syms: BTreeSet::new(),
            reducible_fun_syms: BTreeSet::new(),
            irreducible_fun_syms_fast: tamarin_utils::FastSet::default(),
            reducible_fun_syms_fast: tamarin_utils::FastSet::default(),
            fun_syms_by_name: tamarin_utils::FastMap::default(),
        };
        merged.refresh()
    }
}

/// The name a symbol carries in HS `userDefinedFunSyms`
/// (Term/Maude/Signature.hs:162-164): free and user-defined AC symbols have
/// one, the built-in AC operators, the C symbols and `List` have none and are
/// not part of that signature.
fn user_defined_name(sym: FunSym) -> Option<&'static [u8]> {
    match sym {
        FunSym::NoEq(s) => Some(s.name),
        FunSym::Ac(AcSym::AcFct(s)) => Some(s.name),
        FunSym::Ac(_) | FunSym::C(_) | FunSym::List => None,
    }
}

/// HS `attrsNDC` (Term/Maude/Signature.hs:289): the NDC attributes a symbol prints, in
/// trace-then-diff order (a symbol with `IsNdcBoth` prints both).
fn ndc_attrs(ndc: NdcState) -> &'static [&'static str] {
    match ndc {
        NdcState::NotNdc => &[],
        NdcState::IsNdc => &["NDC"],
        NdcState::IsNdcDiff => &["NDC-diff"],
        NdcState::IsNdcBoth => &["NDC", "NDC-diff"],
    }
}

/// HS `showAttrs` (Term/Maude/Signature.hs:291-292): nothing at all for an empty
/// attribute list, otherwise ` [a1,a2,…]` — note the LEADING space.
fn show_attrs(attrs: &[&str]) -> String {
    if attrs.is_empty() {
        String::new()
    } else {
        format!(" [{}]", attrs.join(","))
    }
}

/// HS `removeIfNecessary'` (Term/Maude/Signature.hs:147-150): if `to_add` is a
/// member of `st2`, drop `to_remove` from `st1` before unioning `st2` in.
/// Union is left-biased, as `S.union` is.
fn remove_if_necessary_prime<T: Ord + Clone>(
    st1: &BTreeSet<T>,
    st2: &BTreeSet<T>,
    to_add: &T,
    to_remove: &T,
) -> BTreeSet<T> {
    let mut out = st1.clone();
    if st2.contains(to_add) {
        out.remove(to_remove);
    }
    out.extend(st2.iter().cloned());
    out
}

/// HS `removeIfNecessary` (Term/Maude/Signature.hs:146): run
/// `removeIfNecessary'` once each way round, so `x` and `y` are mutually
/// exclusive in the result.
fn remove_if_necessary<T: Ord + Clone>(
    st1: &BTreeSet<T>,
    st2: &BTreeSet<T>,
    x: &T,
    y: &T,
) -> BTreeSet<T> {
    let s = remove_if_necessary_prime(st1, st2, x, y);
    remove_if_necessary_prime(&s, st2, y, x)
}

/// HS `unionExceptPairSym` (Term/Maude/Signature.hs:143).
///
/// The `fst`/`snd` constructor and destructor variants are mutually
/// exclusive: whichever variant `st2` carries WINS, and the opposite
/// variant is removed from `st1`.  This is asymmetric in `st2`, matching
/// HS's monoid `<>` (where the right operand is the newly-added symbol).
fn union_except_pair_sym(a: &BTreeSet<NoEqSym>, b: &BTreeSet<NoEqSym>) -> BTreeSet<NoEqSym> {
    let after_fst = remove_if_necessary(a, b, &fst_sym(), &fst_dest_sym());
    remove_if_necessary(&after_fst, b, &snd_sym(), &snd_dest_sym())
}

/// HS `unionExceptPairRules` (Term/Maude/Signature.hs:144).
///
/// The constructor/destructor pair REWRITE RULES are mutually exclusive
/// exactly like the symbols (`unionExceptPairSym`).  Without this, merging
/// `pairing` (`fstRule`/`sndRule`) with `dest-pairing` (`fstDestRule`/
/// `sndDestRule`) would keep BOTH variants, emitting both `fst` rewrite
/// variants and diverging the reducible/irreducible sets from Haskell.
///
/// Note the rule version's `removeIfNecessary` argument order differs
/// from the symbol version: `fstDestRule fstRule` (vs `fstSym fstDestSym`)
/// and `sndRule sndDestRule` — mirrored faithfully below.
fn union_except_pair_rules(
    a: &BTreeSet<CtxtStRule>,
    b: &BTreeSet<CtxtStRule>,
) -> BTreeSet<CtxtStRule> {
    let after_fst = remove_if_necessary(a, b, &fst_dest_rule(), &fst_rule());
    remove_if_necessary(&after_fst, b, &snd_rule(), &snd_dest_rule())
}

// =============================================================================
// Predefined signatures
// =============================================================================

/// HS writes every builtin signature as `maudeSig $ mempty {…}`
/// (Term/Maude/Signature.hs:199-231): a record update of `mempty` handed to
/// the smart constructor.  This macro is that shape in Rust — the named fields
/// over `MaudeSig::default()`, then [`MaudeSig::refresh`].
macro_rules! maude_sig {
    ($($field:ident : $value:expr),* $(,)?) => {
        MaudeSig { $($field: $value,)* ..MaudeSig::default() }.refresh()
    };
}

pub fn dh_maude_sig() -> MaudeSig {
    maude_sig!(enable_dh: true)
}
pub fn bp_maude_sig() -> MaudeSig {
    maude_sig!(enable_bp: true)
}
pub fn mset_maude_sig() -> MaudeSig {
    maude_sig!(enable_mset: true)
}
pub fn nat_maude_sig() -> MaudeSig {
    maude_sig!(enable_nat: true)
}
pub fn xor_maude_sig() -> MaudeSig {
    maude_sig!(enable_xor: true)
}

pub fn pair_maude_sig() -> MaudeSig {
    maude_sig!(st_fun_syms: pair_fun_sig(), st_rules: pair_rules().into())
}

/// `pairDestMaudeSig` (Term/Maude/Signature.hs:221): the `dest-pairing` variant —
/// fst/snd are DESTRUCTORS (`pair_fun_dest_sig`) with the destructor
/// rewrite rules (`pair_dest_rules`), rather than constructors.
pub fn pair_dest_maude_sig() -> MaudeSig {
    maude_sig!(st_fun_syms: pair_fun_dest_sig(), st_rules: pair_dest_rules().into())
}

/// Hash is one-way: no rewrite rules.
pub fn hash_maude_sig() -> MaudeSig {
    maude_sig!(st_fun_syms: hash_fun_sig())
}

pub fn sym_enc_maude_sig() -> MaudeSig {
    maude_sig!(st_fun_syms: sym_enc_fun_sig(), st_rules: sym_enc_rules().into())
}

pub fn asym_enc_maude_sig() -> MaudeSig {
    maude_sig!(st_fun_syms: asym_enc_fun_sig(), st_rules: asym_enc_rules().into())
}

pub fn signature_maude_sig() -> MaudeSig {
    maude_sig!(st_fun_syms: signature_fun_sig(), st_rules: signature_rules().into())
}

pub fn reveal_signature_maude_sig() -> MaudeSig {
    maude_sig!(st_fun_syms: reveal_signature_fun_sig(), st_rules: reveal_signature_rules().into())
}

pub fn location_report_maude_sig() -> MaudeSig {
    maude_sig!(st_fun_syms: location_report_fun_sig(), st_rules: location_report_rules().into())
}

pub fn sym_enc_dest_maude_sig() -> MaudeSig {
    maude_sig!(st_fun_syms: sym_enc_fun_dest_sig(), st_rules: sym_enc_dest_rules().into())
}

pub fn asym_enc_dest_maude_sig() -> MaudeSig {
    maude_sig!(st_fun_syms: asym_enc_fun_dest_sig(), st_rules: asym_enc_dest_rules().into())
}

pub fn signature_dest_maude_sig() -> MaudeSig {
    maude_sig!(st_fun_syms: signature_fun_dest_sig(), st_rules: signature_dest_rules().into())
}

pub fn minimal_maude_sig(diff: bool) -> MaudeSig {
    maude_sig!(enable_diff: diff, st_fun_syms: pair_fun_sig(), st_rules: pair_rules().into())
}

pub fn enable_diff_maude_sig() -> MaudeSig {
    maude_sig!(enable_diff: true)
}

#[cfg(test)]
#[path = "maude_sig_tests.rs"]
mod tests;
