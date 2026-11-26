//! Maude's term order on the module the Maude backend loads, as the ranks the
//! algebra library's port of Maude's unification algorithm takes
//! (`Tamarin.MaudeUnifyExport`). With these ranks the port lists the unifiers
//! Maude lists for the same `unify` command, in Maude's order, with Maude's
//! fresh variables.
//!
//! Maude 3.5.1 compares two operator symbols by `orderInt = symbolCount++ |
//! (arity << 24)`: by arity first, then by creation (`Symbol::compare`). The
//! symbols of the `MSG` module ([`crate::maude_print::pp_theory`]) are created
//! in the order the module declares them, so an operator's rank is its arity
//! and its position in that order ([`module_operators`]). A name constant
//! `f(k)`, `p(k)`, `c(k)`, `n(k)` or `t(k)` has the rank of its operator and
//! the argument `k`. The symbols of the imported `NAT` module come first and
//! are not modelled: only the order among the module's symbols matters.
//!
//! There is one variable symbol per sort and one for the kind, all of arity
//! 0, created after the module's operators the first time a variable of that
//! sort is parsed: first the sorts of the variables of the module's equations
//! in the order the module text writes them, then those of the registration
//! command the Maude backend sends after loading the module (`Msg`, `Fresh`,
//! `Pub`, `Node`, `TOP`, `[TOP]`, then `TamNat` with natural numbers). The
//! fresh variables of unification have the kind.
//!
//! Variables of one variable symbol compare by the code of their name. The
//! Maude backend registers the names `x0, x1, …` in increasing order before
//! any query names them, so the code of `xN` is in the order of `N`: the
//! export takes a variable's identifier as its code, and the caller sends
//! the variable `xN` with identifier `N`.
//!
//! The index of a sort in its connected component orients bindings between
//! variables (`Sort::index`): the kind 0, `TOP` 1, `Msg` 2, `Node` 3, `Pub` 4,
//! `Fresh` 5 and `TamNat` 6, whether or not the module has natural numbers.
//!
//! The rules were established on the captured Maude sessions of the whole
//! corpus, where the port with these ranks reproduced every `unify` reply.

use crate::function_symbols::{
    dh_neutral_sym, exp_sym, inv_sym, nat_one_sym, one_sym, pmult_sym, zero_sym, AcSym, CSym,
    FunSym,
};
use crate::lterm::LSort;
use crate::maude_sig::MaudeSig;
use crate::maude_types::{lterm_to_mterm_global, ConvCtx, MTerm, MaudeLit};
use crate::term::Term;

/// An operator of the `MSG` module.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Operator {
    /// The operator of the name constants of a sort: `f`, `p`, `c`, `n` or `t`.
    Names(LSort),
    /// `list`, `cons` or `nil`, which wrap the arguments of a fact.
    List(&'static str),
    /// A function symbol.
    Symbol(FunSym),
}

impl Operator {
    pub(crate) fn arity(self) -> usize {
        match self {
            Self::Names(_) => 1,
            Self::List("list") => 1,
            Self::List("cons") => 2,
            Self::List(_) => 0,
            Self::Symbol(FunSym::NoEq(s)) => s.arity,
            Self::Symbol(_) => 2,
        }
    }
}

/// The operators of the module of `sig`, in the order the module declares
/// them (`pp_theory`): the name operators, the list operators, the builtin
/// operators of the enabled builtins, the user free symbols and the user AC
/// symbols.
pub(crate) fn module_operators(sig: &MaudeSig) -> Vec<Operator> {
    use Operator::{List, Names, Symbol};
    let mut ops = vec![
        Names(LSort::Fresh),
        Names(LSort::Pub),
        Names(LSort::Msg),
        Names(LSort::Node),
    ];
    if sig.enable_nat {
        ops.push(Names(LSort::Nat));
    }
    ops.extend([List("list"), List("cons"), List("nil")]);
    if sig.enable_mset {
        ops.push(Symbol(FunSym::Ac(AcSym::Union)));
    }
    if sig.enable_dh {
        ops.extend([
            Symbol(FunSym::NoEq(one_sym())),
            Symbol(FunSym::NoEq(dh_neutral_sym())),
            Symbol(FunSym::NoEq(exp_sym())),
            Symbol(FunSym::Ac(AcSym::Mult)),
            Symbol(FunSym::NoEq(inv_sym())),
        ]);
    }
    if sig.enable_bp {
        ops.extend([
            Symbol(FunSym::NoEq(pmult_sym())),
            Symbol(FunSym::C(CSym::EMap)),
        ]);
    }
    if sig.enable_xor {
        ops.extend([
            Symbol(FunSym::NoEq(zero_sym())),
            Symbol(FunSym::Ac(AcSym::Xor)),
        ]);
    }
    if sig.enable_nat {
        ops.extend([
            Symbol(FunSym::NoEq(nat_one_sym())),
            Symbol(FunSym::Ac(AcSym::NatPlus)),
        ]);
    }
    ops.extend(sig.st_fun_syms.iter().map(|s| Symbol(FunSym::NoEq(*s))));
    ops.extend(
        sig.st_ac_fun_syms
            .iter()
            .map(|s| Symbol(FunSym::Ac(AcSym::AcFct(*s)))),
    );
    ops
}

/// A variable symbol of the module.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum VariableSymbol {
    Sort(LSort),
    Top,
    /// The kind `[TOP]`, the sort of the fresh variables of unification.
    Kind,
}

/// The variable symbols of the module of `sig`, in the order Maude creates
/// them: the sorts of the variables of the module's equations by first
/// occurrence in the module text, then those of the Maude backend's
/// registration command.
pub(crate) fn variable_symbols(sig: &MaudeSig) -> Vec<VariableSymbol> {
    use VariableSymbol::{Kind, Sort, Top};
    let mut order = Vec::new();
    let mut add = |v: VariableSymbol| {
        if !order.contains(&v) {
            order.push(v);
        }
    };
    // The module writes each equation as its two sides converted with one
    // context, left side first (`emit_rrule`).
    for rule in sig.rrules() {
        let mut ctx = ConvCtx::new();
        let lhs = lterm_to_mterm_global(&rule.lhs, &mut ctx);
        let rhs = lterm_to_mterm_global(&rule.rhs, &mut ctx);
        for side in [&lhs, &rhs] {
            for_each_variable_sort(side, &mut |s| add(Sort(s)));
        }
    }
    for v in [
        Sort(LSort::Msg),
        Sort(LSort::Fresh),
        Sort(LSort::Pub),
        Sort(LSort::Node),
        Top,
        Kind,
    ] {
        add(v);
    }
    if sig.enable_nat {
        add(Sort(LSort::Nat));
    }
    order
}

/// The sorts of the variables of `t` in the order the module text writes
/// them.
fn for_each_variable_sort(t: &MTerm, f: &mut impl FnMut(LSort)) {
    match t {
        Term::Lit(MaudeLit::MaudeVar(_, s)) => f(*s),
        Term::Lit(_) => {}
        Term::App(_, args) => {
            for a in args.iter() {
                for_each_variable_sort(a, f);
            }
        }
    }
}

/// `Sort::index` of a sort, `None` being the kind.
pub(crate) fn sort_index(s: Option<LSort>) -> u64 {
    match s {
        None => 0,
        Some(LSort::Msg) => 2,
        Some(LSort::Node) => 3,
        Some(LSort::Pub) => 4,
        Some(LSort::Fresh) => 5,
        Some(LSort::Nat) => 6,
    }
}

/// Maude's ranks of the operators and variable symbols of one module.
#[derive(Debug, Clone)]
pub(crate) struct MaudeRanks {
    operators: Vec<(Operator, u64)>,
    variables: Vec<(VariableSymbol, u64)>,
}

impl MaudeRanks {
    pub(crate) fn new(sig: &MaudeSig) -> Self {
        let operators: Vec<_> = module_operators(sig)
            .into_iter()
            .enumerate()
            .map(|(count, op)| (op, ((op.arity() as u64) << 24) | count as u64))
            .collect();
        let created = operators.len() as u64;
        let variables = variable_symbols(sig)
            .into_iter()
            .enumerate()
            .map(|(count, v)| (v, created + count as u64))
            .collect();
        Self {
            operators,
            variables,
        }
    }

    /// The rank of an operator of the module: that of its first declaration.
    pub(crate) fn operator(&self, op: Operator) -> Option<u64> {
        self.operators
            .iter()
            .find(|(o, _)| *o == op)
            .map(|(_, rank)| *rank)
    }

    /// The rank of a variable symbol. Every variable symbol is created by the
    /// registration command.
    pub(crate) fn variable_symbol(&self, v: VariableSymbol) -> Option<u64> {
        self.variables
            .iter()
            .find(|(w, _)| *w == v)
            .map(|(_, rank)| *rank)
    }

    /// The rank rows of the export (`Tamarin.MaudeUnifyExport`) for the
    /// operator ids of `theory`: the free, C and AC symbols by id; the name
    /// operators by sort word; the variable symbols and the sort indices of
    /// the kind and of each sort.
    #[cfg(feature = "lean-unification")]
    pub(crate) fn rows(&self, theory: &crate::lean_unification::Theory) -> [Vec<u64>; 6] {
        let mut rows: [Vec<u64>; 6] = Default::default();
        let set = |row: &mut Vec<u64>, at: usize, rank: u64| {
            if row.len() <= at {
                row.resize(at + 1, 0);
            }
            row[at] = rank;
        };
        let mut seen = tamarin_utils::FastSet::default();
        for (op, rank) in &self.operators {
            if let Operator::Symbol(f) = op
                && seen.insert(*f)
                && let Some((kind, id)) = theory.encode(*f, op.arity())
            {
                set(&mut rows[(kind - 2) as usize], id as usize, *rank);
            }
        }
        const SORTS: [LSort; 5] = [
            LSort::Pub,
            LSort::Fresh,
            LSort::Msg,
            LSort::Node,
            LSort::Nat,
        ];
        for (code, s) in SORTS.into_iter().enumerate() {
            let names = self.operator(Operator::Names(s)).unwrap_or(0);
            set(&mut rows[3], code, names);
        }
        let kind = self.variable_symbol(VariableSymbol::Kind).unwrap_or(0);
        set(&mut rows[4], 0, kind);
        set(&mut rows[5], 0, sort_index(None));
        for (code, s) in SORTS.into_iter().enumerate() {
            let symbol = self.variable_symbol(VariableSymbol::Sort(s)).unwrap_or(0);
            set(&mut rows[4], code + 1, symbol);
            set(&mut rows[5], code + 1, sort_index(Some(s)));
        }
        rows
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::{AcFctSym, Constructability, NdcState, NoEqSym, Privacy};
    use crate::maude_print::pp_theory;
    use crate::maude_sig::{
        bp_maude_sig, dh_maude_sig, hash_maude_sig, minimal_maude_sig, mset_maude_sig,
        nat_maude_sig, sym_enc_maude_sig, xor_maude_sig,
    };

    fn every_builtin() -> MaudeSig {
        let mut sig = minimal_maude_sig(false)
            .merge(dh_maude_sig())
            .merge(xor_maude_sig())
            .merge(bp_maude_sig())
            .merge(mset_maude_sig())
            .merge(nat_maude_sig())
            .merge(hash_maude_sig())
            .merge(sym_enc_maude_sig());
        sig.st_fun_syms.insert(NoEqSym::new(
            "user_f",
            3,
            Privacy::Private,
            Constructability::Constructor,
        ));
        sig.st_ac_fun_syms.insert(AcFctSym::new(
            "combine",
            Privacy::Public,
            Constructability::Constructor,
            NdcState::NotNdc,
        ));
        sig.refresh()
    }

    /// The name and arity of each `op` line of a module text, in order.
    fn declared(text: &str) -> Vec<(String, usize)> {
        text.lines()
            .filter_map(|line| line.trim().strip_prefix("op "))
            .map(|op| {
                let (name, sorts) = op.split_once(" : ").expect("an operator declaration");
                let (args, _) = sorts.split_once("->").expect("a result sort");
                (name.trim().to_owned(), args.split_whitespace().count())
            })
            .collect()
    }

    /// The name the module text gives an operator.
    fn spelled(op: Operator) -> String {
        match op {
            Operator::Names(s) => crate::maude_print::pp_lsort_sym(s).to_owned(),
            Operator::List(name) => name.to_owned(),
            Operator::Symbol(f) => {
                let mut ctx = ConvCtx::new();
                let x = Term::Lit(crate::vterm::Lit::Var(crate::lterm::LVar::new(
                    "x",
                    LSort::Msg,
                    0,
                )));
                let t = crate::term::unsafe_f_app(f, vec![x; op.arity()]);
                let wire = crate::maude_print::pp_mterm(&lterm_to_mterm_global(&t, &mut ctx));
                let wire = String::from_utf8(wire).unwrap();
                wire.split('(').next().unwrap().to_owned()
            }
        }
    }

    /// The order of the operators is the order of the `op` lines of the
    /// module the Maude backend loads, with their arities.
    #[test]
    fn operators_follow_the_declarations_of_the_module_text() {
        for sig in [
            every_builtin(),
            minimal_maude_sig(false),
            minimal_maude_sig(false).merge(xor_maude_sig()).refresh(),
            minimal_maude_sig(false)
                .merge(dh_maude_sig())
                .merge(bp_maude_sig())
                .refresh(),
        ] {
            let ours: Vec<_> = module_operators(&sig)
                .into_iter()
                .map(|op| (spelled(op), op.arity()))
                .collect();
            assert_eq!(ours, declared(&pp_theory(&sig)));
        }
    }

    /// Ranks order by arity, then by declaration; the variable symbols come
    /// after every operator and before every operator with an argument.
    #[test]
    fn ranks_order_by_arity_then_declaration() {
        let sig = every_builtin();
        let ranks = MaudeRanks::new(&sig);
        let one = ranks
            .operator(Operator::Symbol(FunSym::NoEq(one_sym())))
            .unwrap();
        let nil = ranks.operator(Operator::List("nil")).unwrap();
        let fresh = ranks.operator(Operator::Names(LSort::Fresh)).unwrap();
        let list = ranks.operator(Operator::List("list")).unwrap();
        let inv = ranks
            .operator(Operator::Symbol(FunSym::NoEq(inv_sym())))
            .unwrap();
        let union = ranks
            .operator(Operator::Symbol(FunSym::Ac(AcSym::Union)))
            .unwrap();
        let mult = ranks
            .operator(Operator::Symbol(FunSym::Ac(AcSym::Mult)))
            .unwrap();
        let msg = ranks
            .variable_symbol(VariableSymbol::Sort(LSort::Msg))
            .unwrap();
        let kind = ranks.variable_symbol(VariableSymbol::Kind).unwrap();
        assert!(nil < one && one < msg && msg < kind && kind < fresh);
        assert!(fresh < list && list < inv && inv < union && union < mult);
        let order: Vec<_> = variable_symbols(&sig);
        assert_eq!(
            order,
            [
                VariableSymbol::Sort(LSort::Msg),
                VariableSymbol::Sort(LSort::Fresh),
                VariableSymbol::Sort(LSort::Pub),
                VariableSymbol::Sort(LSort::Node),
                VariableSymbol::Top,
                VariableSymbol::Kind,
                VariableSymbol::Sort(LSort::Nat),
            ]
        );
    }

    /// The sorts of the variables of the module's equations come first, in
    /// the order the module text writes them.
    #[test]
    fn equation_variables_create_their_symbols_first() {
        let sig = every_builtin();
        let text = pp_theory(&sig);
        let mut written = Vec::new();
        for line in text.lines().filter(|l| l.trim_start().starts_with("eq ")) {
            for piece in line.split(':').skip(1) {
                let sort = piece
                    .split(|c: char| !c.is_ascii_alphabetic())
                    .next()
                    .unwrap();
                let s = match sort {
                    "Msg" => LSort::Msg,
                    "Fresh" => LSort::Fresh,
                    "Pub" => LSort::Pub,
                    "Node" => LSort::Node,
                    "TamNat" => LSort::Nat,
                    _ => continue,
                };
                let v = VariableSymbol::Sort(s);
                if !written.contains(&v) {
                    written.push(v);
                }
            }
        }
        assert!(!written.is_empty());
        assert_eq!(variable_symbols(&sig)[..written.len()], written[..]);
    }
}
