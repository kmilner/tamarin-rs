//! Compile one active rule to constructor patterns with shared parameter slots.
//! Open queries reify the two variant branches. Concrete queries match the
//! same patterns before reifying the rule RHS.
use super::{
    initialize, tamarin_lean_ground_variant, tamarin_lean_reduce_rule_slot,
    tamarin_pairing_variants, Error, Outcome, LEAN_THREAD,
};
use crate::function_symbols::{nat_one_sym, FunSym};
use crate::lean_identity::IdentityTable;
use crate::lterm::{LNTerm, LSort, LVar};
use crate::maude_proc::ApplicationVariant;
use crate::rewriting::RRule;
use crate::term::{map_lits, Term};
use crate::vterm::{vars_vterm_in_order, Lit};
use rustc_hash::FxHashMap;

enum RuleResult {
    Slot(u64),
    Ground(LNTerm),
}

pub(super) struct NarrowingRule {
    // A leaf is a rule-local parameter. Repeated leaves in any argument
    // share their slot. All applications here are declared constructors.
    images: Vec<Term<u64>>,
    // Every leaf in depth-first argument order, including repeated slots.
    keys: Vec<u64>,
    slots: u64,
    positional: bool,
    result: RuleResult,
}

impl NarrowingRule {
    pub(super) fn positional(&self) -> bool {
        self.positional
    }

    pub(super) fn from_rule(
        rule: &RRule<LNTerm>,
        constructor: impl Fn(FunSym) -> bool,
    ) -> Option<Self> {
        let Term::App(FunSym::NoEq(head), args) = &rule.lhs else {
            return None;
        };
        fn ground(term: &LNTerm, constructor: &impl Fn(FunSym) -> bool) -> bool {
            matches!(term, Term::App(FunSym::NoEq(f), children) if
                *f != nat_one_sym() && constructor(FunSym::NoEq(*f)) && f.arity == children.len()
                && children.iter().all(|t| ground(t, constructor)))
        }
        // At least one constructor is needed for d(x1,...,xn) itself to be
        // normal. Every admitted symbol below has Msg inputs and output.
        if head.arity != args.len()
            || *head == nat_one_sym()
            || !args.iter().any(|arg| matches!(arg, Term::App(..)))
        {
            return None;
        }

        fn encode(
            term: &LNTerm,
            constructor: &impl Fn(FunSym) -> bool,
            vars: &mut IdentityTable<LVar>,
            keys: &mut Vec<u64>,
        ) -> Option<Term<u64>> {
            match term {
                Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg => {
                    let slot = vars.intern(*v)?;
                    keys.push(slot);
                    Some(Term::Lit(slot))
                }
                Term::App(f, args)
                    if constructor(*f)
                        && match f {
                            FunSym::NoEq(head) => {
                                *head != nat_one_sym() && head.arity == args.len()
                            }
                            FunSym::C(_) => args.len() == 2,
                            FunSym::Ac(ac) => args.len() >= 2 && super::ac_sort(*ac) == LSort::Msg,
                            FunSym::List => false,
                        } =>
                {
                    let children = args
                        .iter()
                        .map(|arg| encode(arg, constructor, vars, keys))
                        .collect::<Option<Vec<_>>>()?;
                    Some(Term::App(*f, children.into()))
                }
                _ => None,
            }
        }

        let mut vars = IdentityTable::default();
        let mut keys = Vec::new();
        let images = args
            .iter()
            .map(|arg| encode(arg, &constructor, &mut vars, &mut keys))
            .collect::<Option<Vec<_>>>()?;
        let positional = images
            .iter()
            .all(|t| t.all_fun_syms(|f| matches!(f, FunSym::NoEq(_))));
        let result = match &rule.rhs {
            Term::Lit(Lit::Var(v)) => RuleResult::Slot(vars.id(*v)?),
            rhs if positional && !keys.is_empty() && ground(rhs, &constructor) => {
                RuleResult::Ground(rhs.clone())
            }
            _ => return None,
        };
        Some(Self {
            images,
            keys,
            slots: u64::try_from(vars.len()).ok()?,
            result,
            positional,
        })
    }

    pub(super) fn variants(
        &self,
        terms: &[LNTerm],
        application: &LNTerm,
        args: &[LNTerm],
        normal_message: impl Fn(&LNTerm) -> bool,
    ) -> Result<Outcome, Error> {
        if !self.positional {
            // Substitution-only decoding requires a unique reconstructed result.
            return Ok(Outcome::Unsupported);
        }
        if matches!(self.result, RuleResult::Ground(_)) {
            initialize()?;
            return LEAN_THREAD
                .with(|_| self.ground_variants(terms, application, args, normal_message));
        }
        let Some(observed) = self.open_arguments(args) else {
            return Ok(Outcome::Unsupported);
        };
        if !terms.iter().all(|t| {
            t == application || matches!(t, Term::Lit(Lit::Var(v)) if observed.contains(v))
        }) {
            return Ok(Outcome::Unsupported);
        }
        let (images, _) = self.open_images(&observed)?;
        let bindings = observed.into_iter().zip(images).collect();
        Ok(Outcome::Complete(vec![Vec::new(), bindings]))
    }

    fn open_arguments(&self, args: &[LNTerm]) -> Option<Vec<LVar>> {
        if args.len() != self.images.len() {
            return None;
        }
        let mut observed = Vec::with_capacity(args.len());
        for term in args {
            let Term::Lit(Lit::Var(v)) = term else {
                return None;
            };
            if v.sort != LSort::Msg || observed.contains(v) {
                return None;
            }
            observed.push(*v);
        }
        Some(observed)
    }

    // Both decoders use the same fresh renaming for every occurrence of a slot.
    fn open_images(&self, observed: &[LVar]) -> Result<(Vec<LNTerm>, u64), Error> {
        initialize()?;
        let mask = LEAN_THREAD.with(|_| {
            // SAFETY: the audited export takes and returns one scalar.
            unsafe { tamarin_pairing_variants(1) }
        });
        if mask != 3 {
            return Err(Error::InvalidStatus(mask));
        }
        let max = observed.iter().map(|v| v.idx).max().unwrap_or(0);
        max.checked_add(self.slots)
            .ok_or(Error::FreshVariableOverflow)?;
        let first = max + 1;
        let images = self
            .images
            .iter()
            .map(|p| {
                map_lits(p, &mut |slot| {
                    Lit::Var(LVar::new("x", LSort::Msg, first + slot))
                })
            })
            .collect();
        Ok((images, first))
    }

    /// The caller observes one application value alongside its argument images.
    /// Its action may copy the conclusion after the answer has been chosen.
    pub(super) fn observed_variants(
        &self,
        application: &LNTerm,
        args: &[LNTerm],
    ) -> Result<Option<Vec<ApplicationVariant>>, Error> {
        let RuleResult::Slot(slot) = self.result else {
            return Ok(None);
        };
        let Some(vars) = self.open_arguments(args) else {
            return Ok(None);
        };
        let (images, first) = self.open_images(&vars)?;
        Ok(Some(vec![
            ApplicationVariant {
                bindings: Vec::new(),
                value: application.clone(),
            },
            ApplicationVariant {
                bindings: vars.into_iter().zip(images).collect(),
                value: Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, first + slot))),
            },
        ]))
    }

    fn ground_variants(
        &self,
        terms: &[LNTerm],
        application: &LNTerm,
        args: &[LNTerm],
        normal_message: impl Fn(&LNTerm) -> bool,
    ) -> Result<Outcome, Error> {
        let mut variables = IdentityTable::default();
        for t in terms {
            if t != application && !matches!(t, Term::Lit(_)) {
                return Ok(Outcome::Unsupported);
            }
            for v in vars_vterm_in_order(t) {
                if variables.intern(v).is_none() {
                    return Ok(Outcome::Unsupported);
                }
            }
        }
        let mut holes = Vec::new();
        let mut anchors = Vec::new();
        let mut deps = Vec::new();
        let mut patterns = FxHashMap::default();
        let mut fixed = FxHashMap::default();
        let mut rigid = false;
        for (arg, pattern) in args.iter().zip(&self.images) {
            match arg {
                Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg => {
                    let Some(id) = variables.id(*v) else {
                        return Ok(Outcome::Unsupported);
                    };
                    holes.push(id);
                    patterns.insert(*v, pattern);
                    rigid |= matches!(pattern, Term::App(..));
                }
                _ => {
                    let Term::Lit(slot) = pattern else {
                        return Ok(Outcome::Unsupported);
                    };
                    if !normal_message(arg) || !arg.all_fun_syms(|f| matches!(f, FunSym::NoEq(_))) {
                        return Ok(Outcome::Unsupported);
                    }
                    anchors.push(*slot);
                    fixed.insert(*slot, arg);
                    for v in vars_vterm_in_order(arg) {
                        let Some(id) = variables.id(v) else {
                            return Ok(Outcome::Unsupported);
                        };
                        deps.push(id);
                    }
                }
            }
        }
        // SAFETY: the shim copies all three live slices and returns a scalar
        // mask. Occurrences keep their multiplicity, including duplicate holes
        // or fixed slots; admission of the complete branch belongs to Lean.
        match unsafe {
            tamarin_lean_ground_variant(
                holes.as_ptr(),
                holes.len(),
                anchors.as_ptr(),
                anchors.len(),
                deps.as_ptr(),
                deps.len(),
                u8::from(rigid),
            )
        } {
            0 => return Ok(Outcome::Unsupported),
            3 => {}
            status => return Err(Error::InvalidStatus(status)),
        }

        #[derive(Clone, Copy, Eq, Hash, PartialEq)]
        enum Witness {
            Local(u64),
            Copied(LVar),
        }
        // Maude's back-converter names witnesses "x" and allocates them in
        // first-occurrence order in the answer. Match that alpha-renaming for
        // stable printed rule variants. Only input vars with that hint can
        // collide with these new variables, even when index numbers coincide.
        let mut last = variables
            .values()
            .iter()
            .filter(|v| v.name == "x")
            .map(|v| v.idx)
            .max()
            .unwrap_or(0);
        let mut assigned = FxHashMap::default();
        let mut fresh = |key: Witness| -> Result<LNTerm, Error> {
            let sort = match key {
                Witness::Local(_) => LSort::Msg,
                Witness::Copied(v) => v.sort,
            };
            let var = match assigned.entry(key) {
                std::collections::hash_map::Entry::Occupied(e) => *e.get(),
                std::collections::hash_map::Entry::Vacant(e) => {
                    last = last.checked_add(1).ok_or(Error::FreshVariableOverflow)?;
                    *e.insert(LVar::new("x", sort, last))
                }
            };
            Ok(Term::Lit(Lit::Var(var)))
        };

        fn instantiate<A>(
            t: &Term<A>,
            leaf: &mut impl FnMut(&A) -> Result<LNTerm, Error>,
        ) -> Result<LNTerm, Error> {
            match t {
                Term::Lit(lit) => leaf(lit),
                Term::App(f, args) => {
                    let children = args
                        .iter()
                        .map(|a| instantiate(a, leaf))
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(Term::App(*f, children.into()))
                }
            }
        }

        let mut bindings = Vec::with_capacity(variables.len());
        for &v in variables.values() {
            let image = match patterns.get(&v) {
                Some(pattern) => instantiate(pattern, &mut |slot| match fixed.get(slot) {
                    Some(term) => instantiate(term, &mut |lit| match lit {
                        Lit::Var(w) => fresh(Witness::Copied(*w)),
                        Lit::Con(c) => Ok(Term::Lit(Lit::Con(*c))),
                    }),
                    None => fresh(Witness::Local(*slot)),
                })?,
                None => fresh(Witness::Copied(v))?,
            };
            bindings.push((v, image));
        }
        Ok(Outcome::Complete(vec![Vec::new(), bindings]))
    }

    pub(super) fn reduce(
        &self,
        args: &[LNTerm],
        normal_message: impl Fn(&LNTerm) -> bool,
    ) -> Result<Option<LNTerm>, Error> {
        fn collect<'a>(
            pattern: &Term<u64>,
            subject: &'a LNTerm,
            terms: &mut IdentityTable<&'a LNTerm>,
            subjects: &mut Vec<u64>,
            normal_message: &impl Fn(&LNTerm) -> bool,
        ) -> Result<bool, Error> {
            match (pattern, subject) {
                (Term::Lit(_), term) if normal_message(term) => {
                    subjects.push(terms.intern(term).ok_or(Error::InvalidStatus(255))?);
                }
                (Term::App(f, patterns), Term::App(g, children))
                    if f == g && patterns.len() == children.len() =>
                {
                    for (p, t) in patterns.iter().zip(children.iter()) {
                        if !collect(p, t, terms, subjects, normal_message)? {
                            return Ok(false);
                        }
                    }
                }
                _ => return Ok(false),
            }
            Ok(true)
        }

        if !self.positional {
            return Ok(None);
        }
        if self.images.len() != args.len() {
            return Err(Error::InvalidStatus(255));
        }
        let mut terms = IdentityTable::default();
        let mut subjects = Vec::with_capacity(self.keys.len());
        for (pattern, term) in self.images.iter().zip(args) {
            if !collect(pattern, term, &mut terms, &mut subjects, &normal_message)? {
                return Ok(None);
            }
        }
        if subjects.len() != self.keys.len() {
            return Err(Error::InvalidStatus(255));
        }
        initialize()?;
        LEAN_THREAD.with(|_| {
            let mut selected = 0;
            // SAFETY: both slices have the checked length. The C
            // shim copies the IDs and writes at most one result word.
            match unsafe {
                tamarin_lean_reduce_rule_slot(
                    match self.result {
                        RuleResult::Slot(slot) => slot,
                        RuleResult::Ground(_) => self.keys[0],
                    },
                    self.keys.as_ptr(),
                    subjects.as_ptr(),
                    subjects.len(),
                    &mut selected,
                )
            } {
                0 => Ok(None),
                1 => {
                    let chosen = terms.get(selected).ok_or(Error::InvalidSubject(selected))?;
                    Ok(Some(match &self.result {
                        RuleResult::Slot(_) => super::canonical_capture(chosen),
                        RuleResult::Ground(value) => value.clone(),
                    }))
                }
                status => Err(Error::InvalidStatus(status)),
            }
        })
    }
}
