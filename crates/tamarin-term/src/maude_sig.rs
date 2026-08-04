// Currently GPL 3.0 until granted permission by the following authors:
//   jdreier, beschmi, rkunnema, meiersi, PhilipLukertWork,
//   ValentinYuri, BTom-GH, charlie-j, racoucho1u, rsasse, and other
//   minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Builtin/Rules.hs,
//   lib/term/src/Term/Maude/Signature.hs,
//   lib/theory/src/Theory/Text/Parser/Macro.hs,
//   lib/theory/src/Theory/Text/Parser/Signature.hs,
//   lib/theory/src/Theory/Text/Parser/Term.hs

//! Port of `Term.Maude.Signature` from
//! `lib/term/src/Term/Maude/Signature.hs`.
//!
//! `MaudeSig` describes the equational theory the prover is configured
//! with — which built-in AC operators are enabled (DH, BP, MSet, Nat,
//! XOR), plus user-supplied subterm rules.

use std::collections::BTreeSet;

use crate::builtin::{
    asym_enc_fun_dest_sig, asym_enc_fun_sig, bp_rules, dh_rules, hash_fun_sig,
    location_report_fun_sig, mset_rules, reveal_signature_fun_sig, signature_fun_dest_sig,
    signature_fun_sig, sym_enc_fun_dest_sig, sym_enc_fun_sig, xor_rules,
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

/// HS `stRules :: S.Set CtxtStRule` (Signature.hs:99), paired with the
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

    /// Refresh the cached `fun_syms` / `irreducible_fun_syms` /
    /// `reducible_fun_syms` from the source-of-truth flags.
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

    /// HS `userDefinedFunSyms`: every free symbol of the signature plus every
    /// user-defined AC symbol, tagged with which kind it is.
    ///
    /// Intentionally retained: faithful mirror of HS `userDefinedFunSyms`
    /// (Term/Maude/Signature.hs:163-164).  No call site in the port — HS calls
    /// it from the parser (Theory/Text/Parser/Macro.hs:43,
    /// Theory/Text/Parser/Term.hs:65), whereas the port resolves operator
    /// names from tables of its own: the infix `[AC]` levels off
    /// `parser.rs::ac_fun_syms`, and `lookupArity`'s arity / privacy /
    /// constructability / NDC off `elaborate.rs::CollectedUserFuns`.
    /// [`MaudeSig::user_defined_st_fun_syms`] is the variant intruder-rule
    /// generation uses.
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
    /// (Term/Maude/Signature.hs:152-154) — the `<>` routes through
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
        // HS `<>` (Signature.hs:120-141) rebuilds via `maudeSig (mempty {...})`,
        // and `mempty` has `eqConvergent=False` (line 145), which `maudeSig`
        // preserves (line 105).  So routing through the monoid RESETS
        // eqConvergent to false; mirror that here.
        self.eq_convergent = false;
        self.refresh()
    }

    /// Join `ndc_state` onto the NDC state of every symbol in the subterm
    /// signature whose NAME matches `fun_sym`'s.
    ///
    /// HS `joinNDCinSig` (Signature.hs:233-247) matches by name only, because
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
        let name = match fun_sym {
            FunSym::NoEq(s) => s.name,
            FunSym::Ac(AcSym::AcFct(s)) => s.name,
            _ => return self,
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
    /// (Signature.hs:249-295): the subterm signature's free symbols rendered
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
    /// (Signature.hs:157-159) routes through the monoid `<>`, which rebuilds
    /// from `mempty` (eqConvergent=False, line 145; preserved by `maudeSig`,
    /// line 105) and so RESETS eqConvergent to false — match that.
    pub fn add_macro_sym(mut self, sym: NoEqSym) -> Self {
        self.macro_names.insert(sym);
        self.eq_convergent = false;
        self.refresh()
    }

    /// Add a context subterm rule.
    pub fn add_ctxt_st_rule(mut self, rule: CtxtStRule) -> Self {
        // HS-faithful pair mutual-exclusion (`unionExceptPairRules`,
        // Term/Maude/Signature.hs:135-141): the fst/snd CONSTRUCTOR and
        // DESTRUCTOR rule variants are mutually exclusive.  HS `addCtxtStRule`
        // (Signature.hs:162-164) is `msig <> mempty {stRules=[str]}`, so each
        // user `equations:` rule goes through the monoid `<>`, which applies
        // `unionExceptPairRules` (Signature.hs:120-141, see line 130, 135-141) — it is NOT a plain
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
            // HS `<>` unions `stACFunSyms` plainly (Signature.hs:127-141): the
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
        };
        merged.refresh()
    }
}

/// HS `attrsNDC` (Signature.hs:290): the NDC attributes a symbol prints, in
/// trace-then-diff order (a symbol with `IsNdcBoth` prints both).
fn ndc_attrs(ndc: NdcState) -> &'static [&'static str] {
    match ndc {
        NdcState::NotNdc => &[],
        NdcState::IsNdc => &["NDC"],
        NdcState::IsNdcDiff => &["NDC-diff"],
        NdcState::IsNdcBoth => &["NDC", "NDC-diff"],
    }
}

/// HS `showAttrs` (Signature.hs:292-293): nothing at all for an empty
/// attribute list, otherwise ` [a1,a2,…]` — note the LEADING space.
fn show_attrs(attrs: &[&str]) -> String {
    if attrs.is_empty() {
        String::new()
    } else {
        format!(" [{}]", attrs.join(","))
    }
}

/// HS `unionExceptPairSym` (Term/Maude/Signature.hs:134-141):
///
///   unionExceptPairSym st1 st2 =
///       removeIfNecessary (removeIfNecessary st1 st2 fstSym fstDestSym)
///                         st2 sndSym sndDestSym
///   removeIfNecessary st1 st2 x y =
///       removeIfNecessary' (removeIfNecessary' st1 st2 x y) st2 y x
///   removeIfNecessary' st1 st2 toAdd toRemove =
///       if toAdd `member` st2 then union (delete toRemove st1) st2
///                             else union st1 st2
///
/// The `fst`/`snd` constructor and destructor variants are mutually
/// exclusive: whichever variant `st2` carries WINS, and the opposite
/// variant is removed from `st1`.  This is asymmetric in `st2`, matching
/// HS's monoid `<>` (where the right operand is the newly-added symbol).
fn union_except_pair_sym(a: &BTreeSet<NoEqSym>, b: &BTreeSet<NoEqSym>) -> BTreeSet<NoEqSym> {
    // removeIfNecessary' st1 st2 toAdd toRemove
    fn remove_if_necessary_prime(
        st1: &BTreeSet<NoEqSym>,
        st2: &BTreeSet<NoEqSym>,
        to_add: &NoEqSym,
        to_remove: &NoEqSym,
    ) -> BTreeSet<NoEqSym> {
        if st2.contains(to_add) {
            let mut out: BTreeSet<NoEqSym> = st1.clone();
            out.remove(to_remove);
            out.extend(st2.iter().copied());
            out
        } else {
            st1.union(st2).copied().collect()
        }
    }
    // removeIfNecessary st1 st2 x y
    fn remove_if_necessary(
        st1: &BTreeSet<NoEqSym>,
        st2: &BTreeSet<NoEqSym>,
        x: &NoEqSym,
        y: &NoEqSym,
    ) -> BTreeSet<NoEqSym> {
        let s = remove_if_necessary_prime(st1, st2, x, y);
        remove_if_necessary_prime(&s, st2, y, x)
    }
    let after_fst = remove_if_necessary(a, b, &fst_sym(), &fst_dest_sym());
    remove_if_necessary(&after_fst, b, &snd_sym(), &snd_dest_sym())
}

/// HS `unionExceptPairRules` (Term/Maude/Signature.hs:135-141):
///
///   unionExceptPairRules st1 st2 =
///       removeIfNecessary (removeIfNecessary st1 st2 fstDestRule fstRule)
///                         st2 sndRule sndDestRule
///
/// The constructor/destructor pair REWRITE RULES are mutually exclusive
/// exactly like the symbols (`unionExceptPairSym`): whichever variant
/// `st2` (the right/newly-added operand) carries WINS, and the opposite
/// variant is removed from `st1`.  Without this, merging `pairing`
/// (`fstRule`/`sndRule`) with `dest-pairing` (`fstDestRule`/`sndDestRule`)
/// would keep BOTH variants, emitting both `fst` rewrite variants and
/// diverging the reducible/irreducible sets from Haskell.
///
/// Note the rule version's `removeIfNecessary` argument order differs
/// from the symbol version: `fstDestRule fstRule` (vs `fstSym fstDestSym`)
/// and `sndRule sndDestRule` — mirrored faithfully below.
fn union_except_pair_rules(
    a: &BTreeSet<CtxtStRule>,
    b: &BTreeSet<CtxtStRule>,
) -> BTreeSet<CtxtStRule> {
    // removeIfNecessary' st1 st2 toAdd toRemove
    fn remove_if_necessary_prime(
        st1: &BTreeSet<CtxtStRule>,
        st2: &BTreeSet<CtxtStRule>,
        to_add: &CtxtStRule,
        to_remove: &CtxtStRule,
    ) -> BTreeSet<CtxtStRule> {
        if st2.contains(to_add) {
            let mut out: BTreeSet<CtxtStRule> = st1.clone();
            out.remove(to_remove);
            out.extend(st2.iter().cloned());
            out
        } else {
            st1.union(st2).cloned().collect()
        }
    }
    // removeIfNecessary st1 st2 x y
    fn remove_if_necessary(
        st1: &BTreeSet<CtxtStRule>,
        st2: &BTreeSet<CtxtStRule>,
        x: &CtxtStRule,
        y: &CtxtStRule,
    ) -> BTreeSet<CtxtStRule> {
        let s = remove_if_necessary_prime(st1, st2, x, y);
        remove_if_necessary_prime(&s, st2, y, x)
    }
    let after_fst = remove_if_necessary(a, b, &fst_dest_rule(), &fst_rule());
    remove_if_necessary(&after_fst, b, &snd_rule(), &snd_dest_rule())
}

// The four individual constructor/destructor pair rules
// (Term/Builtin/Rules.hs:101-104), used only by `union_except_pair_rules`.
// `pair_rules`/`pair_dest_rules` in builtin.rs build the *sets*; these
// reconstruct the individual `CtxtStRule`s so the union dedup can target
// them precisely.
fn fst_rule() -> CtxtStRule {
    use crate::builtin::{fst, msg_var, pair};
    use crate::subterm_rule::StRhs;
    let x1 = msg_var("x", 1);
    let x2 = msg_var("x", 2);
    CtxtStRule::new(
        fst(pair(x1.clone(), x2.clone())),
        StRhs {
            positions: vec![vec![0, 0]],
            term: x1,
        },
    )
}
fn snd_rule() -> CtxtStRule {
    use crate::builtin::{msg_var, pair, snd};
    use crate::subterm_rule::StRhs;
    let x1 = msg_var("x", 1);
    let x2 = msg_var("x", 2);
    CtxtStRule::new(
        snd(pair(x1.clone(), x2.clone())),
        StRhs {
            positions: vec![vec![0, 1]],
            term: x2,
        },
    )
}
fn fst_dest_rule() -> CtxtStRule {
    use crate::builtin::{msg_var, pair};
    use crate::subterm_rule::StRhs;
    use crate::term::f_app_no_eq;
    let x1 = msg_var("x", 1);
    let x2 = msg_var("x", 2);
    CtxtStRule::new(
        f_app_no_eq(fst_dest_sym(), vec![pair(x1.clone(), x2.clone())]),
        StRhs {
            positions: vec![vec![0, 0]],
            term: x1,
        },
    )
}
fn snd_dest_rule() -> CtxtStRule {
    use crate::builtin::{msg_var, pair};
    use crate::subterm_rule::StRhs;
    use crate::term::f_app_no_eq;
    let x1 = msg_var("x", 1);
    let x2 = msg_var("x", 2);
    CtxtStRule::new(
        f_app_no_eq(snd_dest_sym(), vec![pair(x1.clone(), x2.clone())]),
        StRhs {
            positions: vec![vec![0, 1]],
            term: x2,
        },
    )
}

// =============================================================================
// Predefined signatures
// =============================================================================

pub fn dh_maude_sig() -> MaudeSig {
    MaudeSig {
        enable_dh: true,
        ..MaudeSig::default()
    }
    .refresh()
}
pub fn bp_maude_sig() -> MaudeSig {
    MaudeSig {
        enable_bp: true,
        ..MaudeSig::default()
    }
    .refresh()
}
pub fn mset_maude_sig() -> MaudeSig {
    MaudeSig {
        enable_mset: true,
        ..MaudeSig::default()
    }
    .refresh()
}
pub fn nat_maude_sig() -> MaudeSig {
    MaudeSig {
        enable_nat: true,
        ..MaudeSig::default()
    }
    .refresh()
}
pub fn xor_maude_sig() -> MaudeSig {
    MaudeSig {
        enable_xor: true,
        ..MaudeSig::default()
    }
    .refresh()
}

pub fn pair_maude_sig() -> MaudeSig {
    MaudeSig {
        st_fun_syms: pair_fun_sig(),
        st_rules: crate::builtin::pair_rules().into(),
        ..MaudeSig::default()
    }
    .refresh()
}

/// `pairDestMaudeSig` (Signature.hs:202-202): the `dest-pairing` variant —
/// fst/snd are DESTRUCTORS (`pair_fun_dest_sig`) with the destructor
/// rewrite rules (`pair_dest_rules`), rather than constructors.
pub fn pair_dest_maude_sig() -> MaudeSig {
    MaudeSig {
        st_fun_syms: pair_fun_dest_sig(),
        st_rules: crate::builtin::pair_dest_rules().into(),
        ..MaudeSig::default()
    }
    .refresh()
}

pub fn hash_maude_sig() -> MaudeSig {
    MaudeSig {
        st_fun_syms: hash_fun_sig(),
        // Hash is one-way: no destructor rules.
        ..MaudeSig::default()
    }
    .refresh()
}

pub fn sym_enc_maude_sig() -> MaudeSig {
    MaudeSig {
        st_fun_syms: sym_enc_fun_sig(),
        st_rules: crate::builtin::sym_enc_rules().into(),
        ..MaudeSig::default()
    }
    .refresh()
}

pub fn asym_enc_maude_sig() -> MaudeSig {
    MaudeSig {
        st_fun_syms: asym_enc_fun_sig(),
        st_rules: crate::builtin::asym_enc_rules().into(),
        ..MaudeSig::default()
    }
    .refresh()
}

pub fn signature_maude_sig() -> MaudeSig {
    MaudeSig {
        st_fun_syms: signature_fun_sig(),
        st_rules: crate::builtin::signature_rules().into(),
        ..MaudeSig::default()
    }
    .refresh()
}

pub fn reveal_signature_maude_sig() -> MaudeSig {
    MaudeSig {
        st_fun_syms: reveal_signature_fun_sig(),
        st_rules: crate::builtin::reveal_signature_rules().into(),
        ..MaudeSig::default()
    }
    .refresh()
}

pub fn location_report_maude_sig() -> MaudeSig {
    MaudeSig {
        st_fun_syms: location_report_fun_sig(),
        st_rules: crate::builtin::location_report_rules().into(),
        ..MaudeSig::default()
    }
    .refresh()
}

pub fn sym_enc_dest_maude_sig() -> MaudeSig {
    MaudeSig {
        st_fun_syms: sym_enc_fun_dest_sig(),
        st_rules: crate::builtin::sym_enc_dest_rules().into(),
        ..MaudeSig::default()
    }
    .refresh()
}

pub fn asym_enc_dest_maude_sig() -> MaudeSig {
    MaudeSig {
        st_fun_syms: asym_enc_fun_dest_sig(),
        st_rules: crate::builtin::asym_enc_dest_rules().into(),
        ..MaudeSig::default()
    }
    .refresh()
}

pub fn signature_dest_maude_sig() -> MaudeSig {
    MaudeSig {
        st_fun_syms: signature_fun_dest_sig(),
        st_rules: crate::builtin::signature_dest_rules().into(),
        ..MaudeSig::default()
    }
    .refresh()
}

pub fn minimal_maude_sig(diff: bool) -> MaudeSig {
    MaudeSig {
        enable_diff: diff,
        st_fun_syms: pair_fun_sig(),
        st_rules: crate::builtin::pair_rules().into(),
        ..MaudeSig::default()
    }
    .refresh()
}

pub fn enable_diff_maude_sig() -> MaudeSig {
    MaudeSig {
        enable_diff: true,
        ..MaudeSig::default()
    }
    .refresh()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dh_signature_includes_dh_rules() {
        let sig = dh_maude_sig();
        assert!(sig.enable_dh);
        assert_eq!(sig.rrules().len(), 13);
    }

    #[test]
    fn bp_implies_dh() {
        let sig = bp_maude_sig();
        // bp turns on dh in refresh().
        assert!(sig.enable_dh);
        // 13 dh + 3 bp = 16
        assert_eq!(sig.rrules().len(), 16);
    }

    #[test]
    fn merge_combines_flags() {
        let merged = dh_maude_sig().merge(xor_maude_sig());
        assert!(merged.enable_dh);
        assert!(merged.enable_xor);
        // 13 dh + 3 xor = 16
        assert_eq!(merged.rrules().len(), 16);
    }

    #[test]
    fn empty_signature_has_no_rules() {
        let sig = MaudeSig::default().refresh();
        assert!(sig.rrules().is_empty());
    }

    /// HS `addFunSym`/`addMacroSym` route through the monoid `<>`
    /// (Signature.hs:152-159), which rebuilds from `mempty`
    /// (eqConvergent=False, line 145) and so RESETS eqConvergent to false.
    ///
    /// Probed against the real prover (v1.13.0): a `functions:` block placed
    /// AFTER an `equations [convergent]:` block prints `equations:` (the
    /// convergent flag is dropped), whereas `functions:` BEFORE keeps
    /// `equations [convergent]:`.  `add_ctxt_st_rule` must NOT reset, since
    /// elaborate.rs sets eq_convergent before the rule loop (mirroring the HS
    /// parser's explicit re-set AFTER `foldl addCtxtStRule`,
    /// Theory/Text/Parser/Signature.hs:226-227).
    #[test]
    fn add_fun_sym_resets_eq_convergent() {
        use crate::function_symbols::{Constructability, NoEqSym, Privacy};
        let sig = MaudeSig {
            eq_convergent: true,
            ..MaudeSig::default()
        };
        let g = NoEqSym::new(
            b"g".to_vec(),
            1,
            Privacy::Public,
            Constructability::Constructor,
        );
        let sig = sig.add_fun_sym(UserDefinedSym::NoEqUser(g));
        assert!(
            !sig.eq_convergent,
            "add_fun_sym must reset eq_convergent (HS monoid <>)"
        );
    }

    #[test]
    fn add_macro_sym_resets_eq_convergent() {
        use crate::function_symbols::{Constructability, NoEqSym, Privacy};
        let sig = MaudeSig {
            eq_convergent: true,
            ..MaudeSig::default()
        };
        let m = NoEqSym::new(
            b"m".to_vec(),
            1,
            Privacy::Private,
            Constructability::Destructor,
        );
        let sig = sig.add_macro_sym(m);
        assert!(
            !sig.eq_convergent,
            "add_macro_sym must reset eq_convergent (HS monoid <>)"
        );
    }

    /// `add_ctxt_st_rule` must PRESERVE eq_convergent (no reset), because the
    /// Rust elaborator sets eq_convergent BEFORE the add_ctxt_st_rule loop
    /// (elaborate.rs's `TheoryItem::Equations` arm), then refreshes — matching
    /// the printed `equations [convergent]:` for the normal
    /// functions-before-equations corpus ordering.
    #[test]
    fn add_ctxt_st_rule_preserves_eq_convergent() {
        let sig = MaudeSig {
            eq_convergent: true,
            ..MaudeSig::default()
        };
        let sig = sig.add_ctxt_st_rule(fst_dest_rule());
        assert!(
            sig.eq_convergent,
            "add_ctxt_st_rule must NOT reset eq_convergent"
        );
    }

    /// An `[AC]` symbol goes to `st_ac_fun_syms` and reaches the derived
    /// signature as `AC (ACfct …)` (HS `maudeSig`'s
    /// `S.union S.map (AC . ACfct) stACFunSyms`).
    #[test]
    fn add_fun_sym_routes_ac_symbols() {
        let f = AcFctSym::new(
            b"f".to_vec(),
            Privacy::Public,
            Constructability::Constructor,
            NdcState::NotNdc,
        );
        let sig = MaudeSig::default().add_fun_sym(UserDefinedSym::AcFctUser(f));
        assert!(sig.st_fun_syms.is_empty());
        assert!(sig.st_ac_fun_syms.contains(&f));
        assert!(sig.fun_syms.contains(&FunSym::Ac(AcSym::AcFct(f))));
        assert_eq!(sig.ac_user_fun_syms().len(), 1);
        assert!(sig
            .user_defined_st_fun_syms()
            .contains(&UserDefinedSym::AcFctUser(f)));
        // A user-defined AC symbol makes the theory an AC theory.
        assert!(!sig.has_no_ac_operators());
    }

    /// HS `ppFunSymb`/`showAttrs` (Signature.hs:273-293): attributes are
    /// bracketed after a LEADING space, free symbols print
    /// `[private,constructor]` where AC symbols print only `[private]`, and the
    /// NDC attributes come last.
    #[test]
    fn pretty_fun_syms_renders_attributes() {
        let sig = MaudeSig {
            st_fun_syms: [
                NoEqSym::new(
                    b"h".to_vec(),
                    1,
                    Privacy::Public,
                    Constructability::Constructor,
                ),
                NoEqSym::new(
                    b"p".to_vec(),
                    2,
                    Privacy::Private,
                    Constructability::Constructor,
                )
                .with_ndc(NdcState::IsNdcBoth),
            ]
            .into_iter()
            .collect(),
            st_ac_fun_syms: [
                AcFctSym::new(
                    b"ac".to_vec(),
                    Privacy::Public,
                    Constructability::Constructor,
                    NdcState::NotNdc,
                ),
                AcFctSym::new(
                    b"pac".to_vec(),
                    Privacy::Private,
                    Constructability::Constructor,
                    NdcState::IsNdc,
                ),
            ]
            .into_iter()
            .collect(),
            ..MaudeSig::default()
        }
        .refresh();
        assert_eq!(
            sig.pretty_fun_syms_except(&UserDefinedSig::new()),
            vec![
                "h/1".to_string(),
                "p/2 [private,constructor,NDC,NDC-diff]".to_string(),
                "ac/2 [AC]".to_string(),
                "pac/2 [private,AC,NDC]".to_string(),
            ]
        );
    }

    /// `xorr(x, x) = zeroo` with `xorr/2 [AC]` — an st rule whose LHS is
    /// Ac-headed, so `term_ac_c_free` is false for it.
    fn ac_headed_st_rule() -> CtxtStRule {
        let xorr = AcFctSym::new(
            b"xorr".to_vec(),
            Privacy::Public,
            Constructability::Constructor,
            NdcState::IsNdc,
        );
        let zeroo = NoEqSym::new(
            b"zeroo".to_vec(),
            0,
            Privacy::Public,
            Constructability::Constructor,
        );
        let x = crate::builtin::msg_var("x", 0);
        let lhs = crate::term::f_app_acfct(xorr, vec![x.clone(), x]);
        let rhs: LNTerm = crate::term::f_app_no_eq(zeroo, vec![]);
        crate::subterm_rule::rrule_to_ctxt_st_rule(&RRule::new(lhs, rhs))
            .expect("ground-RHS st rule")
    }

    /// Every flag `st_rules` hands out describes the rule it is paired with —
    /// through `add_ctxt_st_rule`, through a bare `insert`, and after a
    /// `remove` that shifts the surviving rules' positions.
    #[test]
    fn st_rules_pair_every_rule_with_its_own_lhs_flag() {
        fn flags_match(rules: &StRules) -> bool {
            rules
                .iter_with_lhs_ac_c_free()
                .all(|(r, f)| f == crate::maude_proc::term_ac_c_free(&r.lhs))
        }
        let sig = pair_maude_sig();
        assert!(flags_match(&sig.st_rules));
        assert!(sig.st_lhs_all_ac_c_free());

        let mut sig = sig.add_ctxt_st_rule(ac_headed_st_rule());
        assert!(flags_match(&sig.st_rules));
        assert!(
            !sig.st_lhs_all_ac_c_free(),
            "the Ac-headed LHS must show up"
        );

        // Mutating the `pub` field directly, with no `refresh` afterwards:
        // the flags follow a removal and a re-insertion that together leave
        // the rule count unchanged.
        assert!(sig.st_rules.remove(&fst_rule()));
        assert!(flags_match(&sig.st_rules));
        assert!(sig.st_rules.insert(snd_dest_rule()));
        assert!(flags_match(&sig.st_rules));
        assert!(!sig.st_lhs_all_ac_c_free());
    }

    /// `merge` carries the flags of the united rule set.
    #[test]
    fn merge_keeps_the_lhs_flags_with_their_rules() {
        let ac_sig = MaudeSig {
            st_rules: [ac_headed_st_rule()].into_iter().collect(),
            ..MaudeSig::default()
        }
        .refresh();
        let merged = pair_maude_sig().merge(ac_sig);
        assert!(merged
            .st_rules
            .iter_with_lhs_ac_c_free()
            .all(|(r, f)| f == crate::maude_proc::term_ac_c_free(&r.lhs)));
        assert!(!merged.st_lhs_all_ac_c_free());
    }

    /// HS `joinNDCinSig` (Signature.hs:236-246) is a record update over
    /// `stFunSyms`/`stACFunSyms` that does NOT re-run `maudeSig`, so every
    /// derived cache keeps its pre-join NDC states — and `ndc` participates in
    /// `NoEqSym`/`AcFctSym` `Eq`/`Ord`, so those are DIFFERENT symbols, not the
    /// same symbol read twice.
    ///
    /// This pins the staleness the port inherits, so that adding a `refresh()`
    /// to `join_ndc_in_sig` fails here rather than silently diverging:
    ///   * `fun_syms` (and `no_eq_fun_syms`/`ac_user_fun_syms`/the
    ///     irreducible+reducible sets read off it) keep `NotNdc`;
    ///   * `user_defined_st_fun_syms` (HS `userDefinedSTFunSyms`,
    ///     Signature.hs:166-167) reads the joined `st_fun_syms` for its free
    ///     half but the stale `acUserFunSyms` (Signature.hs:160-161) for its AC
    ///     half, so with one name carried by both a free and an `[AC]` symbol
    ///     the two halves disagree about NDC.
    #[test]
    fn join_ndc_in_sig_leaves_every_derived_cache_stale() {
        let f_free = NoEqSym::new(
            b"f".to_vec(),
            1,
            Privacy::Public,
            Constructability::Constructor,
        );
        let f_ac = AcFctSym::new(
            b"f".to_vec(),
            Privacy::Public,
            Constructability::Constructor,
            NdcState::NotNdc,
        );
        let sig = MaudeSig {
            st_fun_syms: [f_free].into_iter().collect(),
            st_ac_fun_syms: [f_ac].into_iter().collect(),
            ..MaudeSig::default()
        }
        .refresh();
        let joined = sig.join_ndc_in_sig(FunSym::NoEq(f_free), NdcState::IsNdc);

        // Source of truth: both subterm-signature sets are joined, by NAME.
        let f_free_ndc = f_free.with_ndc(NdcState::IsNdc);
        let f_ac_ndc = f_ac.with_ndc(NdcState::IsNdc);
        assert!(joined.st_fun_syms.contains(&f_free_ndc));
        assert!(joined.st_ac_fun_syms.contains(&f_ac_ndc));

        // Derived caches: untouched, i.e. still carrying the pre-join symbols.
        assert!(joined.fun_syms.contains(&FunSym::NoEq(f_free)));
        assert!(joined.fun_syms.contains(&FunSym::Ac(AcSym::AcFct(f_ac))));
        assert!(!joined.fun_syms.contains(&FunSym::NoEq(f_free_ndc)));
        assert!(!joined
            .fun_syms
            .contains(&FunSym::Ac(AcSym::AcFct(f_ac_ndc))));
        assert!(joined.no_eq_fun_syms().contains(&f_free));
        assert!(joined.ac_user_fun_syms().contains(&f_ac));
        assert!(joined.irreducible_fun_syms.contains(&FunSym::NoEq(f_free)));
        assert!(joined
            .irreducible_fun_syms_fast
            .contains(&FunSym::NoEq(f_free)));

        // The two halves of `user_defined_st_fun_syms` disagree about `f`.
        let user_st = joined.user_defined_st_fun_syms();
        assert!(user_st.contains(&UserDefinedSym::NoEqUser(f_free_ndc)));
        assert!(user_st.contains(&UserDefinedSym::AcFctUser(f_ac)));
        assert!(!user_st.contains(&UserDefinedSym::AcFctUser(f_ac_ndc)));

        // `refresh` is what would close the gap — it is deliberately not called
        // by `join_ndc_in_sig`.
        let refreshed = joined.refresh();
        assert!(refreshed.fun_syms.contains(&FunSym::NoEq(f_free_ndc)));
        assert!(refreshed
            .user_defined_st_fun_syms()
            .contains(&UserDefinedSym::AcFctUser(f_ac_ndc)));
    }
}
