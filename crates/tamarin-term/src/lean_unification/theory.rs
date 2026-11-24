//! The theory of a Tamarin file as the `tamarin_theory_*` exports take it
//! (`Tamarin.Theory.Signature` in the Lean library): which equational
//! builtins are enabled, the arities of the other free symbols and the number
//! of user AC symbols. The exports build the declarations of every symbol and
//! the rules of the enabled builtins from these words themselves.
//!
//! Symbol ids are fixed by that specification. Free, C and AC symbols have
//! separate id spaces. The builtin symbols have the small ids below, user
//! free symbol `i` has id `16 + i` and user AC symbol `j` has id `16 + j`.
//! The user symbols are numbered in the order in which the signature's
//! ordered set of declared operators lists them, so every session over one
//! signature, and every worker of a session, uses the same ids.
//!
//! What is decided here and trusted: which Rust symbol a fixed id names, the
//! flags, and the arity of each user free symbol.

use crate::function_symbols::{
    dh_neutral_sym, exp_sym, inv_sym, nat_one_sym, one_sym, pmult_sym, zero_sym, AcSym, CSym,
    FunSym,
};
use crate::lterm::LSort;
use crate::maude_sig::MaudeSig;
use rustc_hash::FxHashMap;

/// Kind words of the declarations and node rows.
const FREE: u64 = 2;
const C: u64 = 3;
const AC: u64 = 4;

/// Flag words (`Theory.Signature.flags`).
const DH: u64 = 1;
const XOR: u64 = 2;
const BP: u64 = 4;
const MSET: u64 = 8;
const NAT: u64 = 16;

/// First id of the user symbols (`Theory.base`).
const BASE: u64 = 16;

/// Bound on the number of user free symbols, on their arities and on the
/// number of user AC symbols (`Theory.limit`).
const LIMIT: usize = 4096;

/// The builtin symbols of the builtins enabled by `flags`, with their kind
/// and fixed id (`Theory.Free`, `Theory.AC`, `Theory.C`).
fn builtins(flags: u64) -> Vec<(FunSym, u64, u64)> {
    let mut symbols = Vec::new();
    if flags & DH != 0 {
        symbols.extend([
            (FunSym::NoEq(exp_sym()), FREE, 0),
            (FunSym::NoEq(inv_sym()), FREE, 1),
            (FunSym::NoEq(one_sym()), FREE, 2),
            (FunSym::NoEq(dh_neutral_sym()), FREE, 3),
            (FunSym::Ac(AcSym::Mult), AC, 0),
        ]);
    }
    if flags & XOR != 0 {
        symbols.extend([
            (FunSym::Ac(AcSym::Xor), AC, 1),
            (FunSym::NoEq(zero_sym()), FREE, 4),
        ]);
    }
    if flags & BP != 0 {
        symbols.extend([
            (FunSym::NoEq(pmult_sym()), FREE, 5),
            (FunSym::C(CSym::EMap), C, 0),
        ]);
    }
    if flags & MSET != 0 {
        symbols.push((FunSym::Ac(AcSym::Union), AC, 2));
    }
    if flags & NAT != 0 {
        symbols.extend([
            (FunSym::Ac(AcSym::NatPlus), AC, 3),
            (FunSym::NoEq(nat_one_sym()), FREE, 6),
        ]);
    }
    symbols
}

/// The theory description of one signature and the fixed id of each of its
/// operators.
pub(crate) struct Theory {
    flags: u64,
    free: Vec<u64>,
    ac: u64,
    ids: FxHashMap<FunSym, (u64, u64)>,
    symbols: FxHashMap<(u64, u64), FunSym>,
}

impl Theory {
    /// The description of `sig`. `None` when the description cannot express
    /// the signature: bilinear pairing without Diffie-Hellman, more than
    /// 4096 user free or AC symbols, a free symbol of arity above 4096, or an
    /// operator of a builtin kind whose builtin is not enabled.
    pub(crate) fn new(sig: &MaudeSig) -> Option<Self> {
        if sig.enable_bp && !sig.enable_dh {
            return None;
        }
        let flags = [
            (sig.enable_dh, DH),
            (sig.enable_xor, XOR),
            (sig.enable_bp, BP),
            (sig.enable_mset, MSET),
            (sig.enable_nat, NAT),
        ]
        .into_iter()
        .filter_map(|(on, flag)| on.then_some(flag))
        .sum();
        let mut theory = Self {
            flags,
            free: Vec::new(),
            ac: 0,
            ids: FxHashMap::default(),
            symbols: FxHashMap::default(),
        };
        for (f, kind, id) in builtins(flags) {
            theory.ids.insert(f, (kind, id));
            theory.symbols.insert((kind, id), f);
        }
        for f in sig.declared_fun_syms() {
            if theory.ids.contains_key(&f) {
                continue;
            }
            let (kind, id) = match f {
                FunSym::NoEq(s) => {
                    if s.arity > LIMIT || theory.free.len() >= LIMIT {
                        return None;
                    }
                    theory.free.push(s.arity as u64);
                    (FREE, BASE + theory.free.len() as u64 - 1)
                }
                FunSym::Ac(AcSym::AcFct(_)) => {
                    if theory.ac as usize >= LIMIT {
                        return None;
                    }
                    theory.ac += 1;
                    (AC, BASE + theory.ac - 1)
                }
                FunSym::Ac(_) | FunSym::C(_) | FunSym::List => return None,
            };
            theory.ids.insert(f, (kind, id));
            theory.symbols.insert((kind, id), f);
        }
        Some(theory)
    }

    /// The flags word: dh 1, xor 2, bp 4, mset 8, nat 16.
    pub(crate) fn flags(&self) -> u64 {
        self.flags
    }

    /// The arities of the user free symbols, by id from 16.
    pub(crate) fn free(&self) -> &[u64] {
        &self.free
    }

    /// The number of user AC symbols.
    pub(crate) fn ac(&self) -> u64 {
        self.ac
    }

    /// Whether the signature has the sort of natural numbers.
    pub(crate) fn nat(&self) -> bool {
        self.flags & NAT != 0
    }

    pub(crate) fn declares_sort(&self, sort: LSort) -> bool {
        self.nat() || sort != LSort::Nat
    }

    /// The kind and id of an application of `f` to `width` arguments: a free
    /// symbol takes exactly its arity, a C symbol two and an AC symbol at
    /// least two. `None` for an operator outside the signature.
    pub(crate) fn encode(&self, f: FunSym, width: usize) -> Option<(u64, u64)> {
        let (kind, id) = *self.ids.get(&f)?;
        let fits = match f {
            FunSym::NoEq(s) => width == s.arity,
            FunSym::C(_) => width == 2,
            FunSym::Ac(_) => width >= 2,
            FunSym::List => false,
        };
        fits.then_some((kind, id))
    }

    /// The operator with id `id` of kind `kind`, its declared arity (two
    /// for C and AC symbols) and its sort: nat for the natural-number
    /// symbols, msg for every other.
    pub(crate) fn decode(&self, kind: u64, id: u64) -> Option<(FunSym, usize, LSort)> {
        let f = *self.symbols.get(&(kind, id))?;
        let arity = match f {
            FunSym::NoEq(s) => s.arity,
            _ => 2,
        };
        let sort = match f {
            FunSym::Ac(AcSym::NatPlus) => LSort::Nat,
            FunSym::NoEq(s) if s == nat_one_sym() && self.nat() => LSort::Nat,
            _ => LSort::Msg,
        };
        Some((f, arity, sort))
    }

    /// The description as words, for a key that has to tell theories apart.
    pub(crate) fn words(&self) -> impl Iterator<Item = u64> + '_ {
        [self.flags, self.ac, self.free.len() as u64]
            .into_iter()
            .chain(self.free.iter().copied())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::{AcFctSym, Constructability, NdcState, NoEqSym, Privacy};
    use crate::maude_sig::{
        bp_maude_sig, dh_maude_sig, minimal_maude_sig, mset_maude_sig, nat_maude_sig,
        pair_maude_sig, xor_maude_sig,
    };

    fn user(name: &str, arity: usize) -> NoEqSym {
        NoEqSym::new(name, arity, Privacy::Public, Constructability::Constructor)
    }

    /// The fixed ids of `Tamarin.Theory`, and the sorts of its symbols.
    #[test]
    fn builtin_symbols_have_the_ids_of_the_specification() {
        let sig = minimal_maude_sig(false)
            .merge(dh_maude_sig())
            .merge(xor_maude_sig())
            .merge(bp_maude_sig())
            .merge(mset_maude_sig())
            .merge(nat_maude_sig())
            .refresh();
        let theory = Theory::new(&sig).unwrap();
        assert_eq!(theory.flags(), 31);
        let msg = LSort::Msg;
        for (f, kind, id, sort) in [
            (FunSym::NoEq(exp_sym()), 2, 0, msg),
            (FunSym::NoEq(inv_sym()), 2, 1, msg),
            (FunSym::NoEq(one_sym()), 2, 2, msg),
            (FunSym::NoEq(dh_neutral_sym()), 2, 3, msg),
            (FunSym::NoEq(zero_sym()), 2, 4, msg),
            (FunSym::NoEq(pmult_sym()), 2, 5, msg),
            (FunSym::NoEq(nat_one_sym()), 2, 6, LSort::Nat),
            (FunSym::Ac(AcSym::Mult), 4, 0, msg),
            (FunSym::Ac(AcSym::Xor), 4, 1, msg),
            (FunSym::Ac(AcSym::Union), 4, 2, msg),
            (FunSym::Ac(AcSym::NatPlus), 4, 3, LSort::Nat),
            (FunSym::C(CSym::EMap), 3, 0, msg),
        ] {
            let width = match f {
                FunSym::NoEq(s) => s.arity,
                _ => 2,
            };
            assert_eq!(theory.encode(f, width), Some((kind, id)), "{f:?}");
            assert_eq!(
                theory.decode(kind, id).map(|(g, _, s)| (g, s)),
                Some((f, sort))
            );
        }
        // The free symbols of minimal_maude_sig, pairing among them, are user
        // symbols with ids from 16, in the order of the declared set.
        let users: Vec<_> = sig
            .declared_fun_syms()
            .into_iter()
            .filter(|f| matches!(f, FunSym::NoEq(_)) && theory.ids[f].1 >= BASE)
            .collect();
        assert_eq!(users.len(), theory.free().len());
        for (i, f) in users.iter().enumerate() {
            let FunSym::NoEq(s) = f else { unreachable!() };
            assert_eq!(theory.encode(*f, s.arity), Some((2, 16 + i as u64)));
            assert_eq!(theory.free()[i], s.arity as u64);
        }
        assert!(users.contains(&FunSym::NoEq(crate::function_symbols::pair_sym())));
    }

    #[test]
    fn a_builtin_symbol_is_a_user_symbol_only_without_its_builtin() {
        let one = FunSym::NoEq(one_sym());
        let mut sig = pair_maude_sig();
        sig.st_fun_syms.insert(one_sym());
        let without = Theory::new(&sig.clone().refresh()).unwrap();
        assert_eq!(without.flags(), 0);
        assert!(without.encode(one, 0).unwrap().1 >= BASE);
        let with = Theory::new(&sig.merge(dh_maude_sig()).refresh()).unwrap();
        assert_eq!(with.encode(one, 0), Some((2, 2)));
        assert_eq!(with.free().len() + 1, without.free().len());
        // Without natural numbers the constant 1 is an ordinary msg symbol.
        let mut sig = pair_maude_sig();
        sig.st_fun_syms.insert(nat_one_sym());
        let theory = Theory::new(&sig.refresh()).unwrap();
        let (kind, id) = theory.encode(FunSym::NoEq(nat_one_sym()), 0).unwrap();
        assert!(id >= BASE);
        assert_eq!(theory.decode(kind, id).unwrap().2, LSort::Msg);
    }

    #[test]
    fn user_ac_symbols_are_numbered_from_sixteen() {
        let mut sig = mset_maude_sig();
        let ac = |name: &'static [u8]| {
            AcFctSym::new(
                name,
                Privacy::Public,
                Constructability::Constructor,
                NdcState::NotNdc,
            )
        };
        sig.st_ac_fun_syms.extend([ac(b"join"), ac(b"meet")]);
        let theory = Theory::new(&sig.refresh()).unwrap();
        assert_eq!(theory.ac(), 2);
        assert_eq!(
            theory.encode(FunSym::Ac(AcSym::AcFct(ac(b"join"))), 3),
            Some((4, 16))
        );
        assert_eq!(
            theory.encode(FunSym::Ac(AcSym::AcFct(ac(b"meet"))), 2),
            Some((4, 17))
        );
        assert_eq!(theory.encode(FunSym::Ac(AcSym::Union), 2), Some((4, 2)));
        // An AC application has at least two arguments.
        assert_eq!(theory.encode(FunSym::Ac(AcSym::Union), 1), None);
    }

    /// The rules `Tamarin.Theory` adds for each builtin (`dhRules`, `xorRules`,
    /// `bpRules`), written out in the order of those lists, with Lean's
    /// variable `i` as `x.i`. They are exactly the rules `user_rules` leaves
    /// out, and each list is in the order of Rust's sorted rule set.
    #[test]
    fn lean_builtin_rules_are_the_rules_of_the_rust_builtins() {
        use crate::builtin::{
            bp_rules, dh_neutral, dh_rules, emap, exp, inv, msg_var, mult, one_const, pmult, xor,
            xor_rules, zero_const,
        };
        use crate::rewriting::RRule;
        let [x1, x2, x3] = [1, 2, 3].map(|i| msg_var("x", i));
        let rule = |lhs, rhs| RRule::new(lhs, rhs);
        let dh = vec![
            rule(exp(x1.clone(), one_const()), x1.clone()),
            rule(exp(dh_neutral(), x1.clone()), dh_neutral()),
            rule(
                exp(exp(x1.clone(), x2.clone()), x3.clone()),
                exp(x1.clone(), mult(x2.clone(), x3.clone())),
            ),
            rule(inv(inv(x1.clone())), x1.clone()),
            rule(inv(one_const()), one_const()),
            rule(
                inv(mult(inv(x1.clone()), x2.clone())),
                mult(x1.clone(), inv(x2.clone())),
            ),
            rule(
                mult(x1.clone(), mult(inv(x1.clone()), x2.clone())),
                x2.clone(),
            ),
            rule(mult(x1.clone(), inv(x1.clone())), one_const()),
            rule(mult(x1.clone(), one_const()), x1.clone()),
            rule(
                mult(
                    inv(mult(x1.clone(), x2.clone())),
                    mult(x2.clone(), x3.clone()),
                ),
                mult(inv(x1.clone()), x3.clone()),
            ),
            rule(
                mult(inv(mult(x1.clone(), x2.clone())), x2.clone()),
                inv(x1.clone()),
            ),
            rule(
                mult(inv(x1.clone()), mult(inv(x2.clone()), x3.clone())),
                mult(inv(mult(x1.clone(), x2.clone())), x3.clone()),
            ),
            rule(
                mult(inv(x1.clone()), inv(x2.clone())),
                inv(mult(x1.clone(), x2.clone())),
            ),
        ];
        let xors = vec![
            rule(xor(x1.clone(), x1.clone()), zero_const()),
            rule(xor(x1.clone(), xor(x1.clone(), x2.clone())), x2.clone()),
            rule(xor(x1.clone(), zero_const()), x1.clone()),
        ];
        let bp = vec![
            rule(
                pmult(x3.clone(), pmult(x2.clone(), x1.clone())),
                pmult(mult(x3.clone(), x2.clone()), x1.clone()),
            ),
            rule(pmult(one_const(), x1.clone()), x1.clone()),
            rule(
                emap(x1.clone(), pmult(x2.clone(), x3.clone())),
                exp(emap(x1.clone(), x3.clone()), x2.clone()),
            ),
        ];
        for (name, lean, rust) in [
            ("dh", dh, dh_rules()),
            ("xor", xors, xor_rules()),
            ("bp", bp, bp_rules()),
        ] {
            assert_eq!(lean.len(), rust.len(), "{name}");
            assert_eq!(lean, rust.into_iter().collect::<Vec<_>>(), "{name}");
        }
    }

    #[test]
    fn signatures_outside_the_description_are_refused() {
        let mut lone = pair_maude_sig();
        lone.enable_bp = true;
        assert!(Theory::new(&lone).is_none());
        let mut wide = pair_maude_sig();
        wide.st_fun_syms.insert(user("wide", LIMIT + 1));
        assert!(Theory::new(&wide.refresh()).is_none());
        let mut widest = pair_maude_sig();
        widest.st_fun_syms.insert(user("widest", LIMIT));
        assert!(Theory::new(&widest.refresh()).is_some());
        let mut many = minimal_maude_sig(false);
        let base = Theory::new(&many.clone().refresh()).unwrap().free().len();
        for i in 0..LIMIT - base {
            many.st_fun_syms.insert(user(&format!("f{i}"), 1));
        }
        assert_eq!(
            Theory::new(&many.clone().refresh()).unwrap().free().len(),
            LIMIT
        );
        many.st_fun_syms.insert(user("one_more", 1));
        assert!(Theory::new(&many.refresh()).is_none());
    }
}
