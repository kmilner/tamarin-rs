//! Packed variant queries and root reductions against the active rewrite table.
mod ac_root_exclusion;
mod ac_root_reduce;
mod binary_cancellation;
mod dh_exponent;
mod dh_peer;
mod dh_power;
mod dh_product;
mod flat_xor;
mod subgroups;
mod uniform_reduction;
mod variant_join;
use super::narrowing::NarrowingRule;
use super::{initialize, subsort, tamarin_lean_constructor_variant, Error, Outcome, LEAN_THREAD};
use crate::function_symbols::{nat_one_sym, AcSym, FunSym, NoEqSym};
use crate::lean_identity::IdentityTable;
use crate::lterm::{LNTerm, LSort, LVar};
use crate::maude_sig::MaudeSig;
use crate::maude_types::sort_of_name;
use crate::term::Term;
use crate::vterm::Lit;
use rustc_hash::FxHashMap;
use uniform_reduction::FreeRule;

// Only the identity-variant proof accepts constructor terms at the kind level.
// Narrowing, reduction and ordinary structured unification require sorted inputs.
#[derive(Clone, Copy, PartialEq)]
enum InputDomain {
    Sorted,
    ConstructorKind,
}

pub(crate) struct RuleTable {
    symbols: IdentityTable<FunSym>,
    roots: Vec<u64>,
    // For each free rule head, one fixed-width row per left side. A malformed
    // row disables exclusion for that entire head.
    patterns: FxHashMap<NoEqSym, Option<Vec<u64>>>,
    // Each AC row lists rigid operand heads required by one active left side.
    ac_patterns: FxHashMap<AcSym, Vec<Vec<u64>>>,
    ac_rules: FxHashMap<AcSym, Vec<crate::rewriting::RRule<LNTerm>>>,
    cancellation_units: FxHashMap<AcSym, LNTerm>,
    free_rules: FxHashMap<NoEqSym, Vec<FreeRule>>,
    narrowing: FxHashMap<NoEqSym, NarrowingRule>,
    nat: bool,
    builtin_xor: bool,
    pub(crate) builtin_dh: bool,
}

impl RuleTable {
    pub(crate) fn admits_terms(&self, equations: &[crate::rewriting::Equal<LNTerm>]) -> bool {
        let mut used = Vec::new();
        // The free unifier recognizes the natural constant by its bare name
        // when checking an image's sort. Only the declared Nat constant can
        // use that spelling here.
        let unambiguous = |f: &FunSym| match f {
            FunSym::NoEq(s) if s.name == crate::function_symbols::NAT_ONE_SYM_STRING => {
                self.nat && *s == nat_one_sym()
            }
            _ => true,
        };
        equations.iter().flat_map(|eq| [&eq.lhs, &eq.rhs]).all(|t| {
            used.clear();
            t.all_fun_syms(unambiguous) && self.collect(t, &mut used, InputDomain::Sorted).is_some()
        })
    }

    pub(crate) fn new(sig: &MaudeSig) -> Option<Self> {
        if sig.enable_diff || !sig.macro_names.is_empty() || (sig.enable_bp && !sig.enable_dh) {
            return None;
        }
        let mut symbols = IdentityTable::default();
        // Read the source declarations even if a library caller edited the
        // signature after its last refresh. IDs stay local to this handle.
        let declared = sig.clone().refresh();
        // Maude maps underscores to hyphens in operator names. Two distinct
        // Rust symbols with one wire name could otherwise hide a rule head.
        let named = declared
            .fun_syms
            .iter()
            .filter(|f| matches!(f, FunSym::NoEq(_) | FunSym::Ac(AcSym::AcFct(_))))
            .count();
        if named != declared.fun_syms_by_wire.len() {
            return None;
        }
        for f in declared.fun_syms {
            symbols.intern(f)?;
        }
        let mut by_head = FxHashMap::default();
        // pp_theory emits exactly rrules(), including builtin DH, BP and XOR.
        let rules = sig.rrules();
        let builtin_dh = sig.enable_dh && dh_product::exact_rules(&rules);
        let builtin_xor = sig.enable_xor
            && rules
                .iter()
                .filter(|r| matches!(r.lhs, Term::App(FunSym::Ac(AcSym::Xor), _)))
                .eq(crate::builtin::xor_rules().iter());
        let mut free_rules = FxHashMap::<NoEqSym, Vec<FreeRule>>::default();
        let mut patterns = FxHashMap::default();
        let mut ac_rules = FxHashMap::<_, Vec<_>>::default();
        let mut ac_patterns = FxHashMap::<AcSym, Vec<Vec<u64>>>::default();
        for rule in rules {
            let Term::App(f, ref args) = rule.lhs else {
                return None;
            };
            if let FunSym::NoEq(f) = f {
                let bucket = patterns.entry(f).or_insert_with(|| Some(Vec::new()));
                if args.len() != f.arity {
                    *bucket = None;
                } else if let Some(rows) = bucket {
                    if let Some(candidate) = FreeRule::compile(&rule, rows.len()) {
                        free_rules.entry(f).or_default().push(candidate);
                    }
                    rows.extend(args.iter().map(|arg| head_code(&symbols, arg)));
                }
            }
            if let FunSym::Ac(ac) = f {
                // Omitting a required head only makes exclusion less precise.
                // A raw same-head child contributes its flattened operands.
                let mut row = Vec::new();
                required_factor_heads(&symbols, ac, args, &mut row);
                ac_patterns.entry(ac).or_default().push(row);
                ac_rules.entry(ac).or_default().push(rule.clone());
            }
            by_head
                .entry(f)
                .and_modify(|r| *r = None)
                .or_insert(Some(rule));
        }
        // Maude numbers literal names independently in each equation and query.
        // A declared nullary function carries the same identity in both.
        ac_rules.retain(|_, bucket| {
            bucket
                .iter()
                .all(|rule| !named_literals(&rule.lhs) && !named_literals(&rule.rhs))
        });
        let mut roots = by_head
            .keys()
            .map(|f| symbols.id(*f))
            .collect::<Option<Vec<_>>>()?;
        roots.sort_unstable();
        let narrowing = by_head
            .iter()
            .filter_map(|(f, rule)| {
                let FunSym::NoEq(f) = f else { return None };
                let rule = NarrowingRule::from_rule(rule.as_ref()?, |sym| {
                    symbols.id(sym).is_some() && !by_head.contains_key(&sym)
                })?;
                Some((*f, rule))
            })
            .collect();
        let cancellation_units = ac_rules
            .iter()
            .filter_map(|(&head, bucket)| {
                let unit = binary_cancellation::unit_for(head, bucket)?;
                let Term::App(z, _) = unit else { return None };
                (symbols.id(*z).is_some()
                    && !by_head.contains_key(z)
                    && !(sig.enable_nat && z == &FunSym::NoEq(nat_one_sym())))
                    .then(|| (head, unit.clone()))
            })
            .collect();
        Some(Self {
            cancellation_units,
            symbols,
            roots,
            patterns,
            ac_patterns,
            ac_rules,
            free_rules,
            narrowing,
            nat: sig.enable_nat,
            builtin_dh,
            builtin_xor: builtin_xor
                && !by_head.contains_key(&FunSym::NoEq(crate::function_symbols::zero_sym())),
        })
    }

    pub(super) fn declares_sort(&self, sort: LSort) -> bool {
        self.nat || sort != LSort::Nat
    }

    /// Maude module declarations have homogeneous C/AC operators. The builtin
    /// constant for 1 is the only nullary free operator with a non-Msg result.
    pub(super) fn declaration(&self, f: FunSym) -> Option<(u64, usize, LSort)> {
        let id = self.symbols.id(f)?;
        let (arity, sort) = match f {
            FunSym::NoEq(f) => (
                f.arity,
                if f == nat_one_sym() && self.nat {
                    LSort::Nat
                } else {
                    LSort::Msg
                },
            ),
            FunSym::Ac(ac) => (2, super::ac_sort(ac)),
            FunSym::C(_) => (2, LSort::Msg),
            FunSym::List => return None,
        };
        Some((id, arity, sort))
    }

    fn collect(&self, term: &LNTerm, used: &mut Vec<u64>, domain: InputDomain) -> Option<LSort> {
        let (head, args) = match term {
            Term::Lit(lit) => {
                let sort = match lit {
                    Lit::Var(v) => v.sort,
                    Lit::Con(c) => sort_of_name(c),
                };
                return self.declares_sort(sort).then_some(sort);
            }
            Term::App(f, args) => (*f, args),
        };
        let (id, arity, sort) = self.declaration(head)?;
        let valid_arity = match head {
            FunSym::Ac(_) => args.len() >= arity,
            _ => args.len() == arity,
        };
        if !valid_arity {
            return None;
        }
        used.push(id);
        let expected = if domain == InputDomain::ConstructorKind && sort == LSort::Nat {
            LSort::Msg
        } else {
            sort
        };
        for arg in args.iter() {
            if !subsort(self.collect(arg, used, domain)?, expected) {
                return None;
            }
        }
        Some(sort)
    }

    // A Fresh or Pub variable cannot acquire sort Nat. A Msg variable can.
    // Rigid terms keep their root sort under substitution. The whole query
    // has already passed declaration, kind and arity checks.
    fn nat_factor_codes(&self, factors: &[LNTerm]) -> Option<Vec<u64>> {
        let mut used = Vec::new();
        factors
            .iter()
            .map(|t| {
                used.clear();
                let sort = self.collect(t, &mut used, InputDomain::Sorted)?;
                Some(match (sort, t) {
                    (LSort::Nat, _) => 1,
                    (LSort::Msg, Term::Lit(Lit::Var(_))) => 0,
                    _ => 2,
                })
            })
            .collect()
    }

    fn sort_evidence(&self, t: &LNTerm) -> Option<Vec<u64>> {
        if let Term::App(FunSym::Ac(AcSym::NatPlus), factors) = t {
            self.nat_factor_codes(factors)
        } else {
            self.collect(t, &mut Vec::new(), InputDomain::Sorted)
                .map(|_| vec![1])
        }
    }

    pub(crate) fn unify_kind_sum(
        &self,
        equations: &[crate::rewriting::Equal<LNTerm>],
    ) -> Result<Outcome, Error> {
        let mut used = Vec::new();
        if !self.nat
            || !equations.iter().flat_map(|eq| [&eq.lhs, &eq.rhs]).all(|t| {
                used.clear();
                self.collect(t, &mut used, InputDomain::ConstructorKind)
                    .is_some()
            })
        {
            return Ok(Outcome::Unsupported);
        }
        if equations.iter().all(|eq| eq.lhs == eq.rhs) {
            return super::reflexive_identity();
        }
        for eq in equations {
            let (Some(left), Some(right)) =
                (self.sort_evidence(&eq.lhs), self.sort_evidence(&eq.rhs))
            else {
                continue;
            };
            initialize()?;
            let status = LEAN_THREAD.with(|_| {
                // SAFETY: the shim copies both live slices before calling Lean.
                unsafe {
                    super::tamarin_lean_sort_clash(
                        left.as_ptr(),
                        left.len(),
                        right.as_ptr(),
                        right.len(),
                    )
                }
            });
            match status {
                0 => {}
                1 => return Ok(Outcome::Complete(vec![])),
                other => return Err(Error::InvalidStatus(other)),
            }
        }
        Ok(Outcome::Unsupported)
    }

    fn fresh_xor_pair(&self, t: &LNTerm) -> Option<[LVar; 2]> {
        if !self.builtin_xor {
            return None;
        }
        let Term::App(FunSym::Ac(AcSym::Xor), args) = t else {
            return None;
        };
        let [Term::Lit(Lit::Var(x)), Term::Lit(Lit::Var(y))] = args.as_ref() else {
            return None;
        };
        (x.sort == LSort::Fresh && y.sort == LSort::Fresh).then_some([*x, *y])
    }

    pub(crate) fn observed_application_variants(
        &self,
        t: &LNTerm,
    ) -> Result<Option<Vec<crate::maude_proc::ApplicationVariant>>, Error> {
        let Term::App(FunSym::NoEq(f), args) = t else {
            return Ok(None);
        };
        let Some(rule) = self.narrowing.get(f) else {
            return Ok(None);
        };
        rule.observed_variants(t, args)
    }

    pub(crate) fn fresh_xor_variants(&self, query: &LNTerm) -> Result<Outcome, Error> {
        let terms = match query {
            Term::App(FunSym::List, args) => args.as_ref(),
            _ => std::slice::from_ref(query),
        };
        if let [app] = terms
            && self.flat_xor_args(app).is_some_and(|xs| xs.len() > 2)
        {
            return self.flat_xor_variants(app);
        }
        let Some((app, [x, y])) = terms
            .iter()
            .find_map(|t| self.fresh_xor_pair(t).map(|p| (t, p)))
        else {
            return Ok(Outcome::Unsupported);
        };
        if !terms
            .iter()
            .all(|t| t == app || matches!(t,Term::Lit(Lit::Var(v)) if *v == x || *v == y))
        {
            return Ok(Outcome::Unsupported);
        }
        let mask = xor_branches(x == y)?;
        let mut answers = Vec::new();
        if mask & 1 != 0 {
            answers.push(vec![]);
        }
        if mask & 2 != 0 {
            if x == y {
                // The diagonal is already the identity on the single operand.
                answers.push(vec![]);
            } else {
                let idx = flat_xor::witness_indices(x.idx.max(y.idx), |i| i == x.idx || i == y.idx)
                    .next()
                    .ok_or(Error::FreshVariableOverflow)?;
                let image = Term::Lit(Lit::Var(LVar::new("x", LSort::Fresh, idx)));
                answers.push(vec![(x, image.clone()), (y, image)]);
            }
        }
        Ok(Outcome::Complete(answers))
    }

    pub(crate) fn fresh_xor_reduce(&self, term: &LNTerm) -> Result<Option<LNTerm>, Error> {
        let Some([x, y]) = self.fresh_xor_pair(term) else {
            return self.flat_xor_reduce(term);
        };
        // Distinct free operands are already in normal form. Equal operands
        // have only the diagonal branch, whose normal form is the declared zero.
        Ok(Some(if xor_branches(x == y)? & 1 == 0 {
            crate::builtin::zero_const()
        } else {
            term.clone()
        }))
    }

    /// Use the same normalizer to reconstruct variant values and to decide
    /// whether a later binding made a previously normal observation reducible.
    pub(crate) fn reduce_native(&self, term: &LNTerm) -> Result<Option<LNTerm>, Error> {
        if self
            .collect(term, &mut Vec::new(), InputDomain::Sorted)
            .is_none()
        {
            return Ok(None);
        }
        self.reduce_native_sorted(term)
    }

    fn reduce_native_sorted(&self, term: &LNTerm) -> Result<Option<LNTerm>, Error> {
        tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
        if let Term::App(FunSym::NoEq(f), args) = term
            && !self.patterns.contains_key(f)
        {
            // free_normalForm: every active free rule has a bucket, even when
            // its pattern cannot be compiled. No root step is possible here.
            let mut changed = None;
            for (i, arg) in args.iter().enumerate() {
                let Some(value) = self.reduce_native_sorted(arg)? else {
                    return Ok(None);
                };
                if changed.is_some() || value != *arg {
                    changed
                        .get_or_insert_with(|| args[..i].to_vec())
                        .push(value);
                }
            }
            return Ok(Some(match changed {
                Some(values) => crate::term::f_app_no_eq(*f, values),
                None => term.clone(),
            }));
        }
        if let Term::App(FunSym::Ac(f), args) = term
            && self.guarded_pair(*f, args)
        {
            let mut values = Vec::with_capacity(args.len());
            for child in args.iter() {
                let Some(value) = self.reduce_native_sorted(child)? else {
                    return Ok(None);
                };
                values.push(value);
            }
            return Ok(Some(crate::term::f_app_ac(*f, values)));
        }
        if matches!(term, Term::Lit(_)) {
            return Ok(Some(term.clone()));
        }
        if let Some(normal) = self.fresh_xor_reduce(term)? {
            return Ok(Some(normal));
        }
        if let Some(normal) = self.cancellation_normal(term)? {
            return Ok(Some(normal));
        }
        if let Some(normal) = self.reduce_sorted(term)? {
            return Ok(Some(normal));
        }
        if self.normal_tree(term, false, &mut Some(super::residual::Budget::new()))? {
            return Ok(Some(term.clone()));
        }
        self.ac_root_reduce(term)
    }

    pub(crate) fn reduce(&self, term: &LNTerm) -> Result<Option<LNTerm>, Error> {
        if self
            .collect(term, &mut Vec::new(), InputDomain::Sorted)
            .is_none()
        {
            return Ok(None);
        }
        self.reduce_sorted(term)
    }

    fn reduce_sorted(&self, term: &LNTerm) -> Result<Option<LNTerm>, Error> {
        if let Some(value) = self.dh_power_normal(term)? {
            return Ok(Some(value));
        }
        if let Term::App(FunSym::NoEq(f), args) = term
            && let Some(rule) = self.narrowing.get(f)
            && let Some(value) = rule.reduce(args, |t| self.normal_message(t))?
        {
            return Ok(Some(value));
        }
        if self.irreducible(term)? {
            return Ok(Some(term.clone()));
        }
        if self.builtin_dh
            && self.dh_product_context(term)
            && let Some(value) = self.dh_product_normal(term)?
        {
            return Ok(Some(value));
        }
        self.checked_reduct(term, false)
    }

    /// Rule heads can be excluded either on the current term, or uniformly on
    /// all its normalized sorted instances for an identity variant.
    pub(super) fn irreducible(&self, term: &LNTerm) -> Result<bool, Error> {
        self.normal_tree(term, false, &mut None)
    }

    pub(super) fn stably_normal(&self, term: &LNTerm) -> Result<bool, Error> {
        self.normal_tree(term, true, &mut None)
    }

    pub(super) fn stably_normal_native(&self, term: &LNTerm) -> Result<bool, Error> {
        self.normal_tree(term, true, &mut Some(super::residual::Budget::new()))
    }

    pub(super) fn irreducible_native(&self, term: &LNTerm) -> Result<bool, Error> {
        if self
            .collect(term, &mut Vec::new(), InputDomain::Sorted)
            .is_none()
        {
            return Ok(false);
        }
        self.normal_tree(term, false, &mut Some(super::residual::Budget::new()))
    }

    fn normal_tree(
        &self,
        term: &LNTerm,
        stable: bool,
        budget: &mut Option<super::residual::Budget>,
    ) -> Result<bool, Error> {
        let Term::App(head, args) = term else {
            return Ok(true);
        };
        if !super::canonical_children(head, args) {
            return Ok(false);
        }
        let Some(id) = self.symbols.id(*head) else {
            return Ok(false);
        };
        if self.roots.binary_search(&id).is_ok() {
            let excluded = match head {
                FunSym::NoEq(f) => match self.patterns.get(f) {
                    Some(Some(rows)) => {
                        self.excludes_free_rules(rows, args, stable)?
                            || (!stable
                                && budget.is_some()
                                && self.excludes_free_matches(*f, rows, term)?)
                    }
                    _ => false,
                },
                FunSym::Ac(ac) => {
                    if self.excludes_ac_rules(*ac, args, stable)? {
                        true
                    } else if let Some(budget) = budget {
                        self.excludes_ac_instances(*ac, term, args, budget)?
                    } else {
                        false
                    }
                }
                _ => false,
            };
            if !excluded {
                return Ok(false);
            }
        }
        for arg in args.iter() {
            if !self.normal_tree(arg, stable, budget)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Empty rigid-subject match sets exclude the root only if the compiled
    /// patterns account for every active rule in this bucket.
    fn excludes_free_matches(
        &self,
        f: NoEqSym,
        rows: &[u64],
        term: &LNTerm,
    ) -> Result<bool, Error> {
        let Some(rules) = self.free_rules.get(&f) else {
            return Ok(false);
        };
        if f.arity == 0 || rules.len().checked_mul(f.arity) != Some(rows.len()) {
            return Ok(false);
        }
        for rule in rules {
            let query = crate::rewriting::Equal {
                lhs: rule.pattern().clone(),
                rhs: term.clone(),
            };
            if !matches!(self.match_rigid_subjects(&[query])?, Outcome::Complete(arms) if arms.is_empty())
            {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub(super) fn excludes_free_rules(
        &self,
        rows: &[u64],
        args: &[LNTerm],
        stable: bool,
    ) -> Result<bool, Error> {
        if args.is_empty() || !rows.len().is_multiple_of(args.len()) {
            return Ok(false);
        }
        let Some(heads) = self.subject_heads(args, stable) else {
            return Ok(false);
        };
        initialize()?;
        let status = LEAN_THREAD.with(|_| {
            // SAFETY: each row has the checked subject arity. Both slices
            // remain live while the shim copies them.
            unsafe {
                super::tamarin_lean_exclude_root(
                    rows.as_ptr(),
                    rows.len() / heads.len(),
                    heads.as_ptr(),
                    heads.len(),
                )
            }
        });
        decision(status)
    }

    fn excludes_ac_rules(&self, ac: AcSym, args: &[LNTerm], stable: bool) -> Result<bool, Error> {
        let Some(rows) = self.ac_patterns.get(&ac) else {
            return Ok(false);
        };
        let Some(heads) = self.subject_heads(args, stable) else {
            return Ok(false);
        };
        let slices: Vec<_> = rows.iter().map(|r| super::WordSlice::new(r)).collect();
        initialize()?;
        let status = LEAN_THREAD.with(|_| {
            // SAFETY: the rule table owns all row data. The descriptors and
            // the operand heads remain live through this synchronous call.
            unsafe {
                super::tamarin_lean_exclude_ac_factors(
                    slices.as_ptr(),
                    slices.len(),
                    super::WordSlice::new(&heads),
                )
            }
        });
        decision(status)
    }

    fn subject_heads(&self, args: &[LNTerm], stable: bool) -> Option<Vec<u64>> {
        args.iter().map(|t| {
            // Pub and Fresh have only atom/variable inhabitants in the emitted
            // module. An unrestricted Msg variable could acquire ANY rule head
            // or expand into multiple AC factors after substitution.
            if stable && matches!(t, Term::Lit(Lit::Var(v)) if !matches!(v.sort, LSort::Fresh | LSort::Pub)) {
                None
            } else {
                Some(head_code(&self.symbols, t))
            }
        }).collect()
    }

    // Every operator in this sorted subject must be a constructor for the
    // whole table. User-declared destructors are detected by their equations.
    fn normal_message(&self, term: &LNTerm) -> bool {
        let mut used = Vec::new();
        self.collect(term, &mut used, InputDomain::Sorted)
            .is_some_and(|sort| subsort(sort, LSort::Msg))
            && used.iter().all(|f| self.roots.binary_search(f).is_err())
    }

    pub(crate) fn variants(&self, query: &LNTerm) -> Result<Outcome, Error> {
        let terms = match query {
            Term::App(FunSym::List, args) => args.as_ref(),
            _ => std::slice::from_ref(query),
        };
        let mut used = Vec::new();
        for term in terms {
            if self
                .collect(term, &mut used, InputDomain::ConstructorKind)
                .is_none()
            {
                return Ok(Outcome::Unsupported);
            }
        }
        initialize()?;
        LEAN_THREAD.with(|_| {
            // SAFETY: the shim copies both live slices and consumes the Lean
            // arrays during the call. The export returns a scalar Bool.
            match unsafe {
                tamarin_lean_constructor_variant(
                    self.roots.as_ptr(),
                    self.roots.len(),
                    used.as_ptr(),
                    used.len(),
                )
            } {
                1 => Ok(Outcome::Complete(vec![vec![]])),
                0 => {
                    // The identity theorem admits raw constructor contexts. Other
                    // variant proofs assume sorted terms in every packed position.
                    if !terms.iter().all(|term| {
                        used.clear();
                        self.collect(term, &mut used, InputDomain::Sorted).is_some()
                    }) {
                        return Ok(Outcome::Unsupported);
                    }
                    // Each observation must retain one common identity substitution.
                    // A uniformly selected root step may change its normal value.
                    let mut identity = true;
                    for t in terms {
                        if !self.stably_normal(t)? && self.uniform_reduct(t)?.is_none() {
                            identity = false;
                            break;
                        }
                    }
                    if identity {
                        return Ok(Outcome::Complete(vec![vec![]]));
                    }
                    if let complete @ Outcome::Complete(_) = self.dh_peer_variants(query)? {
                        return Ok(complete);
                    }
                    let Some((rule, application, args)) = terms.iter().find_map(|term| {
                        let Term::App(FunSym::NoEq(f), args) = term else {
                            return None;
                        };
                        Some((self.narrowing.get(f)?, term, args.as_ref()))
                    }) else {
                        return Ok(Outcome::Unsupported);
                    };
                    rule.variants(terms, application, args, |t| self.normal_message(t))
                }
                status => Err(Error::InvalidStatus(status)),
            }
        })
    }
}

// Zero is a wildcard on the pattern side. Literals need no wire identity
// here because only application heads can witness a required rigid head.
pub(super) fn head_code(symbols: &IdentityTable<FunSym>, term: &LNTerm) -> u64 {
    match term {
        Term::App(f, _) => symbols.id(*f).and_then(|id| id.checked_add(1)).unwrap_or(0),
        Term::Lit(_) => 0,
    }
}

fn named_literals(t: &LNTerm) -> bool {
    match t {
        Term::Lit(Lit::Con(_)) => true,
        Term::Lit(Lit::Var(_)) => false,
        Term::App(_, args) => args.iter().any(named_literals),
    }
}

fn required_factor_heads(
    symbols: &IdentityTable<FunSym>,
    ac: AcSym,
    factors: &[LNTerm],
    row: &mut Vec<u64>,
) {
    for t in factors {
        if let Term::App(FunSym::Ac(f), args) = t
            && *f == ac
        {
            required_factor_heads(symbols, ac, args, row);
        } else {
            let code = head_code(symbols, t);
            if code != 0 {
                row.push(code);
            }
        }
    }
}

fn decision(status: u8) -> Result<bool, Error> {
    match status {
        0 => Ok(false),
        1 => Ok(true),
        other => Err(Error::InvalidStatus(other)),
    }
}

fn xor_branches(same: bool) -> Result<u8, Error> {
    initialize()?;
    LEAN_THREAD.with(|_| {
        // SAFETY: the pinned export takes and returns native scalar bytes.
        let mask = unsafe { super::tamarin_xor_branches(u8::from(same)) };
        if (1..=3).contains(&mask) {
            Ok(mask)
        } else {
            Err(Error::InvalidStatus(mask))
        }
    })
}
