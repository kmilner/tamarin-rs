// Currently GPL 3.0 until granted permission by the following authors:
//   beschmi, BTom-GH, charlie-j, PhilipLukertWork, jdreier, meiersi,
//   rsasse, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Builtin/Rules.hs,
//   lib/term/src/Term/Maude/Signature.hs,
//   lib/theory/src/Theory/Text/Parser/Signature.hs

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
    xor_reducible_fun_sig, FunSig, FunSym, NoEqFunSig, NoEqSym,
};
use crate::lterm::LNTerm;
use crate::rewriting::RRule;
use crate::subterm_rule::CtxtStRule;
use crate::term::Term;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct MaudeSig {
    pub enable_dh: bool,
    pub enable_bp: bool,
    pub enable_mset: bool,
    pub enable_nat: bool,
    pub enable_xor: bool,
    pub enable_diff: bool,
    pub st_fun_syms: BTreeSet<NoEqSym>,
    pub st_rules: BTreeSet<CtxtStRule>,
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
    /// (DH / BP / multiset / nat / XOR).  The local Robinson unifier and the
    /// `reduce` identity fast-path are complete only for such signatures; this
    /// is the single source of truth for that "no AC theory" predicate.
    pub fn has_no_ac_operators(&self) -> bool {
        !self.enable_dh
            && !self.enable_bp
            && !self.enable_mset
            && !self.enable_nat
            && !self.enable_xor
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
            .cloned()
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
        self.irreducible_fun_syms_fast = irreducible.iter().cloned().collect();
        self.reducible_fun_syms_fast = reducible.iter().cloned().collect();
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

    /// Add a free function symbol.
    ///
    /// HS `addFunSym funsym msig = msig <> mempty {stFunSyms = [funsym]}`
    /// (Term/Maude/Signature.hs:152-154) — the `<>` routes through
    /// `unionExceptPairSym`, so adding the `fst`/`snd` DESTRUCTOR variant
    /// removes the built-in CONSTRUCTOR variant (and vice versa).  A plain
    /// `insert` would leave BOTH `fst/1` and `fst/1[destructor]` in the set,
    /// printing the symbol twice in the `functions:` header.
    pub fn add_fun_sym(mut self, sym: NoEqSym) -> Self {
        let mut singleton: BTreeSet<NoEqSym> = BTreeSet::new();
        singleton.insert(sym);
        self.st_fun_syms = union_except_pair_sym(&self.st_fun_syms, &singleton);
        // HS `<>` (Signature.hs:120-141) rebuilds via `maudeSig (mempty {...})`,
        // and `mempty` has `eqConvergent=False` (line 145), which `maudeSig`
        // preserves (line 105).  So routing through the monoid RESETS
        // eqConvergent to false; mirror that here.
        self.eq_convergent = false;
        self.refresh()
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
            st_rules: union_except_pair_rules(&self.st_rules, &other.st_rules),
            macro_names: self
                .macro_names
                .union(&other.macro_names)
                .cloned()
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
            out.extend(st2.iter().cloned());
            out
        } else {
            st1.union(st2).cloned().collect()
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
        st_rules: crate::builtin::pair_rules(),
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
        st_rules: crate::builtin::pair_dest_rules(),
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
        st_rules: crate::builtin::sym_enc_rules(),
        ..MaudeSig::default()
    }
    .refresh()
}

pub fn asym_enc_maude_sig() -> MaudeSig {
    MaudeSig {
        st_fun_syms: asym_enc_fun_sig(),
        st_rules: crate::builtin::asym_enc_rules(),
        ..MaudeSig::default()
    }
    .refresh()
}

pub fn signature_maude_sig() -> MaudeSig {
    MaudeSig {
        st_fun_syms: signature_fun_sig(),
        st_rules: crate::builtin::signature_rules(),
        ..MaudeSig::default()
    }
    .refresh()
}

pub fn reveal_signature_maude_sig() -> MaudeSig {
    MaudeSig {
        st_fun_syms: reveal_signature_fun_sig(),
        st_rules: crate::builtin::reveal_signature_rules(),
        ..MaudeSig::default()
    }
    .refresh()
}

pub fn location_report_maude_sig() -> MaudeSig {
    MaudeSig {
        st_fun_syms: location_report_fun_sig(),
        st_rules: crate::builtin::location_report_rules(),
        ..MaudeSig::default()
    }
    .refresh()
}

pub fn sym_enc_dest_maude_sig() -> MaudeSig {
    MaudeSig {
        st_fun_syms: sym_enc_fun_dest_sig(),
        st_rules: crate::builtin::sym_enc_dest_rules(),
        ..MaudeSig::default()
    }
    .refresh()
}

pub fn asym_enc_dest_maude_sig() -> MaudeSig {
    MaudeSig {
        st_fun_syms: asym_enc_fun_dest_sig(),
        st_rules: crate::builtin::asym_enc_dest_rules(),
        ..MaudeSig::default()
    }
    .refresh()
}

pub fn signature_dest_maude_sig() -> MaudeSig {
    MaudeSig {
        st_fun_syms: signature_fun_dest_sig(),
        st_rules: crate::builtin::signature_dest_rules(),
        ..MaudeSig::default()
    }
    .refresh()
}

pub fn minimal_maude_sig(diff: bool) -> MaudeSig {
    MaudeSig {
        enable_diff: diff,
        st_fun_syms: pair_fun_sig(),
        st_rules: crate::builtin::pair_rules(),
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
        let sig = sig.add_fun_sym(g);
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
    /// (elaborate.rs:666 then :683), then refreshes — matching the printed
    /// `equations [convergent]:` for the normal functions-before-equations
    /// corpus ordering.
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
}
