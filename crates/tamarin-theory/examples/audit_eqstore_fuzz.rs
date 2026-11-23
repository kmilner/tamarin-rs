//! Caller-scope differential fuzzer for `EquationStore::apply_eq_store`.
//!
//! The query-level fuzzer (`tamarin-term/examples/audit_fuzz.rs`) compares answer families and
//! cannot see how a caller reads them. `apply_eq_store` reads a unifier's range through the
//! caller's scope: a range variable that is also a system variable is lifted into the domain.
//! A backend whose witnesses share a name with a system variable that merely did not occur
//! in the query therefore changes the store. This tool builds stores the way the solver does
//! (a disjunction of rule variants or of AC unifiers, a free substitution), applies random
//! substitutions that mention bystander system variables named `x` with low indices, and
//! compares the Maude and the native store after every step.
//!
//! Build (from the tamarin-rs root):
//!   cargo build --profile ci -p tamarin-theory --features tamarin-term/lean-unification \
//!     --example audit_eqstore_fuzz
//!
//! Subcommands (binary: target/ci/examples/audit_eqstore_fuzz):
//!   drive  --cfg native|maude --seed S --iters N --out DIR [--seconds WALL]
//!          [--timeout SECS] [--sigs a,b]   runs `worker`, restarts it after a hang or crash,
//!          and stops after WALL seconds; no Maude child outlives a worker
//!   worker (same flags plus --start I)
//!   one    --cfg C --seed S --iter I [--sigs a,b]     replay one generated case verbosely
//!   t6     --cfg C                                     the shape that flipped a verdict
//!
//! Oracles, per `apply_eq_store` step:
//!   differential (subject backend against Maude, from the subject's own previous store):
//!     * the free substitution and the split ids are identical;
//!     * each disjunction covers the other up to renaming of fresh range variables:
//!       every arm of one is an AC-instance of an arm of the other, with system variables
//!       rigid and unbound domain variables standing for themselves;
//!   independent of the other backend (also run on Maude's own store as `maude-*`):
//!     * an arm binds only variables that the applied substitution relates to the arms it
//!       came from (`arm-binds-unrelated-variable`); a witness mistaken for a system
//!       variable shows up here;
//!     * an arm is an AC-instance of some input arm under the new free substitution
//!       (`arm-not-instance-of-input`);
//!     * every binding respects the sort of its variable.
#![allow(clippy::all, clippy::disallowed_macros, dead_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::io::Write as _;
use std::panic::AssertUnwindSafe;
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

use tamarin_term::algebra_backend::AlgebraBackend;
use tamarin_term::builtin;
use tamarin_term::function_symbols::{
    AcFctSym, AcSym, CSym, Constructability, FunSym, NdcState, Privacy,
};
use tamarin_term::lterm::{
    fresh_term, pub_term, sort_compare, sort_of_lnterm, HasFrees, LNTerm, LSort, LVar, NameTag,
};
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::maude_sig::{hash_maude_sig, pair_maude_sig, MaudeSig};
use tamarin_term::rewriting::Equal;
use tamarin_term::subst::apply_vterm;
use tamarin_term::subst_vfresh::LNSubstVFresh;
use tamarin_term::term::{f_app, f_app_ac, Term};
use tamarin_term::vterm::Lit;
use tamarin_theory::tools::equation_store::{EquationStore, LNSubst};

type Sub = Vec<(LVar, LNTerm)>;

// -------------------------------------------------------------------- rng

#[derive(Clone)]
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        let mut z = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^= z >> 31;
        Rng(if z == 0 { 0x1234_5678_9ABC_DEF1 } else { z })
    }
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: usize) -> usize {
        ((self.next() >> 11) % (n.max(1) as u64)) as usize
    }
    fn pct(&mut self, p: usize) -> bool {
        self.below(100) < p
    }
    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }
}

// -------------------------------------------------------------------- terms

fn var(name: &str, sort: LSort, idx: u64) -> LVar {
    LVar::new(name, sort, idx)
}
fn v(x: LVar) -> LNTerm {
    Term::Lit(Lit::Var(x))
}
fn canon(t: &LNTerm) -> LNTerm {
    match t {
        Term::Lit(_) => t.clone(),
        Term::App(s, args) => f_app(*s, args.iter().map(canon).collect()),
    }
}
fn app(t: &LNTerm, m: &BTreeMap<LVar, LNTerm>) -> LNTerm {
    match t {
        Term::Lit(Lit::Var(x)) => m.get(x).map(canon).unwrap_or_else(|| t.clone()),
        Term::Lit(_) => t.clone(),
        Term::App(s, args) => f_app(*s, args.iter().map(|a| app(a, m)).collect()),
    }
}
fn vars_of(t: &LNTerm, out: &mut BTreeSet<LVar>) {
    t.for_each_free(&mut |x| {
        out.insert(*x);
    });
}
fn sort_ok(want: LSort, t: &LNTerm) -> bool {
    matches!(
        sort_compare(sort_of_lnterm(t), want),
        Some(std::cmp::Ordering::Equal | std::cmp::Ordering::Less)
    )
}

fn show_var(x: &LVar, o: &mut String) {
    o.push_str(match x.sort {
        LSort::Msg => "",
        LSort::Fresh => "~",
        LSort::Pub => "$",
        LSort::Nat => "%",
        LSort::Node => "#",
    });
    o.push_str(x.name);
    let _ = write!(o, ".{}", x.idx);
}
fn show_into(t: &LNTerm, o: &mut String) {
    match t {
        Term::Lit(Lit::Var(x)) => show_var(x, o),
        Term::Lit(Lit::Con(n)) => {
            if n.tag == NameTag::Fresh {
                o.push('~');
            }
            let _ = write!(o, "'{}'", n.id.as_str());
        }
        Term::App(s, args) => {
            let name: String = match s {
                FunSym::NoEq(s) => String::from_utf8_lossy(s.name).into_owned(),
                FunSym::Ac(AcSym::Union) => "union".into(),
                FunSym::Ac(AcSym::Mult) => "mult".into(),
                FunSym::Ac(AcSym::Xor) => "xor".into(),
                FunSym::Ac(AcSym::NatPlus) => "tplus".into(),
                FunSym::Ac(AcSym::AcFct(s)) => String::from_utf8_lossy(s.name).into_owned(),
                FunSym::C(CSym::EMap) => "em".into(),
                FunSym::List => "LIST".into(),
            };
            o.push_str(&name);
            if !args.is_empty() {
                o.push('(');
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        o.push(',');
                    }
                    show_into(a, o);
                }
                o.push(')');
            }
        }
    }
}
fn show(t: &LNTerm) -> String {
    let mut o = String::new();
    show_into(t, &mut o);
    o
}
fn show_sub(s: &Sub) -> String {
    let mut o = String::from("{");
    for (i, (x, t)) in s.iter().enumerate() {
        if i > 0 {
            o.push_str(", ");
        }
        show_var(x, &mut o);
        o.push_str(" -> ");
        show_into(t, &mut o);
    }
    o.push('}');
    o
}
fn show_store(s: &EquationStore) -> String {
    let mut o = format!("  subst {}\n", show_sub(&s.subst.to_list()));
    for d in &s.conj {
        let _ = writeln!(o, "  disj {:?} ({} arms)", d.split_id, d.substs.len());
        for a in &d.substs {
            let _ = writeln!(o, "    {}", show_sub(&a.to_list()));
        }
    }
    o
}

// -------------------------------------------------------------------- signatures

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Xor,
    Dh,
    XorDh,
    Mset,
    /// A user-declared AC symbol (`functions: merge/2 [AC]`).
    UserAc,
    /// Bilinear pairing: products, exponentiation, `pmult` and the commutative `em`.
    Bp,
}
fn merge_sym() -> AcFctSym {
    AcFctSym::new(
        b"merge",
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    )
}
struct SigInfo {
    name: &'static str,
    kind: Kind,
    sig: MaudeSig,
}
fn sigs() -> Vec<SigInfo> {
    let mk = |name, kind, f: fn(&mut MaudeSig)| {
        let mut s = pair_maude_sig().merge(hash_maude_sig());
        f(&mut s);
        SigInfo {
            name,
            kind,
            sig: s.refresh(),
        }
    };
    vec![
        mk("xor", Kind::Xor, |s| s.enable_xor = true),
        mk("dh", Kind::Dh, |s| s.enable_dh = true),
        mk("xordh", Kind::XorDh, |s| {
            s.enable_xor = true;
            s.enable_dh = true;
        }),
        mk("mset", Kind::Mset, |s| s.enable_mset = true),
        mk("userac", Kind::UserAc, |s| {
            s.st_ac_fun_syms.insert(merge_sym());
        }),
        mk("bp", Kind::Bp, |s| s.enable_bp = true),
    ]
}

// -------------------------------------------------------------------- generation

struct Gen<'a> {
    rng: &'a mut Rng,
    kind: Kind,
    vars: Vec<LVar>,
}
impl Gen<'_> {
    fn ac(&mut self) -> Option<AcSym> {
        Some(match self.kind {
            Kind::Xor => AcSym::Xor,
            Kind::Dh | Kind::Bp => AcSym::Mult,
            Kind::UserAc => AcSym::AcFct(merge_sym()),
            Kind::XorDh => {
                if self.rng.pct(60) {
                    AcSym::Xor
                } else {
                    AcSym::Mult
                }
            }
            Kind::Mset => AcSym::Union,
        })
    }
    fn leaf(&mut self) -> LNTerm {
        if !self.vars.is_empty() && self.rng.pct(80) {
            v(*self.rng.pick(&self.vars))
        } else if self.rng.pct(70) {
            pub_term(*self.rng.pick(&["a", "b"]))
        } else {
            fresh_term("n")
        }
    }
    /// Constructor terms and AC sums; `reducible` adds exponentiation and inverses.
    fn term(&mut self, depth: usize, reducible: bool) -> LNTerm {
        if depth == 0 || self.rng.pct(25) {
            return self.leaf();
        }
        let r = self.rng.below(100);
        if r < 55 {
            let sym = self.ac().unwrap();
            let n = 2 + usize::from(self.rng.pct(25));
            let args = (0..n).map(|_| self.term(depth - 1, reducible)).collect();
            f_app_ac(sym, args)
        } else if r < 70 && reducible && matches!(self.kind, Kind::Dh | Kind::XorDh | Kind::Bp) {
            if self.kind == Kind::Bp && self.rng.pct(35) {
                builtin::pmult(
                    self.term(depth - 1, reducible),
                    self.term(depth - 1, reducible),
                )
            } else if self.rng.pct(70) {
                builtin::exp(
                    self.term(depth - 1, reducible),
                    self.term(depth - 1, reducible),
                )
            } else {
                builtin::inv(self.term(depth - 1, reducible))
            }
        } else if r < 85 && self.kind == Kind::Bp && self.rng.pct(50) {
            builtin::emap(
                self.term(depth - 1, reducible),
                self.term(depth - 1, reducible),
            )
        } else if r < 85 {
            builtin::pair(
                self.term(depth - 1, reducible),
                self.term(depth - 1, reducible),
            )
        } else {
            builtin::hash(self.term(depth - 1, reducible))
        }
    }
    /// A term a variable of this sort may be bound to.
    fn image(&mut self, sort: LSort, depth: usize) -> LNTerm {
        match sort {
            LSort::Msg => self.term(depth, false),
            LSort::Fresh => {
                let c: Vec<LVar> = self
                    .vars
                    .iter()
                    .copied()
                    .filter(|x| x.sort == LSort::Fresh)
                    .collect();
                if c.is_empty() {
                    fresh_term("n")
                } else {
                    v(*self.rng.pick(&c))
                }
            }
            _ => {
                let c: Vec<LVar> = self
                    .vars
                    .iter()
                    .copied()
                    .filter(|x| x.sort == sort)
                    .collect();
                if c.is_empty() || self.rng.pct(30) {
                    pub_term("a")
                } else {
                    v(*self.rng.pick(&c))
                }
            }
        }
    }
}

/// One generated scenario: a store and the substitutions applied to it in order.
#[derive(Clone)]
struct Case {
    si: usize,
    store: EquationStore,
    steps: Vec<LNSubst>,
}
impl Case {
    fn show(&self, sig: &str) -> String {
        let mut o = format!("sig {sig}\nstore:\n{}", show_store(&self.store));
        for (i, a) in self.steps.iter().enumerate() {
            let _ = writeln!(o, "step {i}: apply {}", show_sub(&a.to_list()));
        }
        o
    }
    fn measure(&self) -> usize {
        self.store
            .conj
            .iter()
            .map(|d| d.substs.len())
            .sum::<usize>()
            * 4
            + self.store.subst.len()
            + self.steps.iter().map(|s| 1 + s.len()).sum::<usize>()
    }
}

/// Bystander system variables: named like Maude witnesses, low indices, never in the rule.
fn bystanders(rng: &mut Rng) -> Vec<LVar> {
    let mut out = Vec::new();
    for i in 0..5 {
        if rng.pct(60) {
            out.push(var("x", LSort::Msg, i));
        }
    }
    if rng.pct(25) {
        out.push(var("x", LSort::Fresh, rng.below(4) as u64));
    }
    if rng.pct(25) {
        out.push(var("y", LSort::Msg, 1 + rng.below(3) as u64));
    }
    if out.is_empty() {
        out.push(var("x", LSort::Msg, 2));
    }
    out
}

fn gen_case(rng: &mut Rng, ctx: &mut Ctx, si: usize) -> Option<Case> {
    let kind = ctx.sigs[si].kind;
    // Rule variables sit above the system variables, as freshly instantiated rules do.
    let base = 5 + rng.below(3) as u64;
    let mut rule_vars = vec![var("x", LSort::Msg, base), var("y", LSort::Msg, base)];
    if rng.pct(40) {
        rule_vars.push(var("u", LSort::Msg, base));
    }
    if rng.pct(20) {
        rule_vars.push(var("k", LSort::Fresh, base));
    }
    let abstraction = var("z", LSort::Msg, base);
    let system = {
        let mut s = vec![
            var("c", LSort::Msg, 0),
            var("e", LSort::Msg, 1),
            var("d", LSort::Msg, 2),
        ];
        if rng.pct(40) {
            s.push(var("k", LSort::Fresh, 0));
        }
        if rng.pct(30) {
            s.push(var("p", LSort::Pub, 1));
        }
        s
    };
    let by = bystanders(rng);

    let mut store = EquationStore::empty();
    // Free substitution: bindings of variables nothing else mentions.
    let mut bound: BTreeSet<LVar> = BTreeSet::new();
    if rng.pct(50) {
        let mut g = Gen {
            rng: &mut *rng,
            kind,
            vars: by.clone(),
        };
        let m = var("m", LSort::Msg, base + 1);
        let img = if g.rng.pct(60) {
            v(*g.rng.pick(&by))
        } else {
            g.term(1, false)
        };
        store.subst = LNSubst::from_list([(m, img)]);
        bound.insert(m);
    }
    // Disjunctions: the variants of a rule term, or the AC unifiers of two terms.
    let n_disj = 1 + usize::from(rng.pct(20));
    for _ in 0..n_disj {
        let arms: Vec<Sub> = if !matches!(kind, Kind::Mset | Kind::UserAc) && rng.pct(70) {
            let mut g = Gen {
                rng: &mut *rng,
                kind,
                vars: rule_vars.clone(),
            };
            // Variants of nested exponentiations are large and slow in Maude.
            let depth = if kind == Kind::Xor {
                1 + g.rng.below(2)
            } else {
                1
            };
            let t = g.term(depth, true);
            let mut tv = BTreeSet::new();
            vars_of(&t, &mut tv);
            if tv.is_empty() {
                return None;
            }
            let vs = ctx.maude(|h| h.variants(&t)).ok()?;
            if vs.len() > 24 {
                return None;
            }
            let mut arms = Vec::new();
            for a in vs {
                let mp: BTreeMap<LVar, LNTerm> = a.iter().cloned().collect();
                let nf = ctx.maude(|h| h.reduce(&app(&t, &mp))).ok()?;
                let mut a: Sub = tv
                    .iter()
                    .map(|x| (*x, mp.get(x).cloned().unwrap_or(v(*x))))
                    .collect();
                // Unbound rule variables keep a private witness, as `extend_with_renaming` does.
                for (x, img) in a.iter_mut() {
                    if *img == v(*x) {
                        *img = v(var("x", x.sort, 90 + x.idx));
                    }
                }
                a.push((abstraction, nf));
                arms.push(a);
            }
            arms
        } else {
            let mut g = Gen {
                rng: &mut *rng,
                kind,
                vars: rule_vars.clone(),
            };
            let (dl, dr) = (1 + g.rng.below(2), 1 + g.rng.below(2));
            let (l, r) = (g.term(dl, false), g.term(dr, false));
            let us = ctx
                .maude(|h| h.unify(&[Equal::new(l.clone(), r.clone())]))
                .ok()?;
            if us.is_empty() || us.len() > 24 {
                return None;
            }
            us
        };
        let arms: Vec<LNSubstVFresh> = arms.into_iter().map(LNSubstVFresh::from_list).collect();
        if arms.iter().all(|a| a.is_empty()) {
            return None;
        }
        store.add_disj(arms);
    }

    // Steps. Every step keeps domain and range disjoint and never rebinds a variable.
    let mut steps = Vec::new();
    let n_steps = 1 + usize::from(rng.pct(75)) + usize::from(rng.pct(35));
    let mut next_extra = base + 2;
    for k in 0..n_steps {
        let mut live: BTreeSet<LVar> = BTreeSet::new();
        for d in &store.conj {
            for a in &d.substs {
                live.extend(a.dom().copied());
            }
        }
        // After the first step the disjunction talks about the system variables.
        if k > 0 {
            live.extend(system.iter().copied());
        }
        live.retain(|x| !bound.contains(x));
        let mut pool: Vec<LVar> = system
            .iter()
            .copied()
            .filter(|x| !bound.contains(x))
            .collect();
        if rng.pct(70) {
            pool.extend(by.iter().copied());
        }
        let mut pairs: Vec<(LVar, LNTerm)> = Vec::new();
        let shape = rng.below(100);
        if shape < 25 && k > 0 {
            // The shape of the verdict flip: bind a variable nothing mentions to a bystander.
            let m = var("m", LSort::Msg, next_extra);
            next_extra += 1;
            let mut g = Gen {
                rng: &mut *rng,
                kind,
                vars: by.clone(),
            };
            let img = if g.rng.pct(70) {
                v(*g.rng.pick(&by))
            } else {
                g.term(1, false)
            };
            pairs.push((m, img));
        } else if shape < 32 && k > 0 {
            // The empty substitution re-unifies every arm unchanged.
        } else {
            let dom: Vec<LVar> = live
                .iter()
                .copied()
                .filter(|x| if k == 0 { !system.contains(x) } else { true })
                .collect();
            for x in dom {
                if !rng.pct(if k == 0 { 65 } else { 30 }) {
                    continue;
                }
                let vars: Vec<LVar> = pool.iter().copied().filter(|y| *y != x).collect();
                let mut g = Gen {
                    rng: &mut *rng,
                    kind,
                    vars,
                };
                let d = if g.rng.pct(70) { 0 } else { 1 };
                let img = g.image(x.sort, d);
                if !sort_ok(x.sort, &img) {
                    continue;
                }
                pairs.push((x, img));
            }
            // Domain and range must be disjoint.
            let dom: BTreeSet<LVar> = pairs.iter().map(|(x, _)| *x).collect();
            pairs.retain(|(_, t)| {
                let mut r = BTreeSet::new();
                vars_of(t, &mut r);
                r.is_disjoint(&dom)
            });
        }
        bound.extend(pairs.iter().map(|(x, _)| *x));
        steps.push(LNSubst::from_list(pairs));
    }
    Some(Case { si, store, steps })
}

/// The scenario from the verdict flip: variants of `x XOR y`, then a bystander binding.
fn t6_case(ctx: &mut Ctx) -> Case {
    let si = ctx.sigs.iter().position(|s| s.name == "xor").unwrap();
    let (x, y, z) = (
        var("x", LSort::Msg, 5),
        var("y", LSort::Msg, 5),
        var("z", LSort::Msg, 5),
    );
    let t = f_app_ac(AcSym::Xor, vec![v(x), v(y)]);
    let mut arms = Vec::new();
    ctx.ensure(si);
    for a in ctx.maude(|h| h.variants(&t)).expect("variants") {
        let mp: BTreeMap<LVar, LNTerm> = a.iter().cloned().collect();
        let nf = ctx.maude(|h| h.reduce(&app(&t, &mp))).expect("reduce");
        let mut a: Sub = [x, y]
            .iter()
            .map(|k| (*k, mp.get(k).cloned().unwrap_or(v(*k))))
            .collect();
        for (k, img) in a.iter_mut() {
            if *img == v(*k) {
                *img = v(var("x", k.sort, 90 + k.idx));
            }
        }
        a.push((z, nf));
        arms.push(LNSubstVFresh::from_list(a));
    }
    let mut store = EquationStore::empty();
    store.add_disj(arms);
    let (c, e, m) = (
        var("c", LSort::Msg, 0),
        var("e", LSort::Msg, 1),
        var("m", LSort::Msg, 6),
    );
    Case {
        si,
        store,
        steps: vec![
            LNSubst::from_list([(x, v(c)), (y, v(e))]),
            LNSubst::from_list([]),
            LNSubst::from_list([(m, v(var("x", LSort::Msg, 2)))]),
        ],
    }
}

// -------------------------------------------------------------------- backends

#[derive(Clone, Copy, PartialEq, Eq)]
enum Cfg {
    Native,
    Maude,
}
impl Cfg {
    fn parse(s: &str) -> Cfg {
        match s {
            "native" => Cfg::Native,
            "maude" => Cfg::Maude,
            _ => panic!("unknown cfg {s}"),
        }
    }
    fn name(self) -> &'static str {
        match self {
            Cfg::Native => "native",
            Cfg::Maude => "maude",
        }
    }
}

const MISSING: &str = "/nonexistent/audit-eqstore-fuzz-native-only-must-not-start-maude";

struct Ctx {
    cfg: Cfg,
    maude_path: String,
    sigs: Vec<SigInfo>,
    cur: usize,
    oracle: Vec<Option<MaudeHandle>>,
    subject: Vec<Option<MaudeHandle>>,
}
impl Ctx {
    fn new(cfg: Cfg) -> Ctx {
        let sigs = sigs();
        let n = sigs.len();
        Ctx {
            cfg,
            maude_path: tamarin_test_support::maude_path().unwrap_or_else(|| "maude".into()),
            sigs,
            cur: 0,
            oracle: (0..n).map(|_| None).collect(),
            subject: (0..n).map(|_| None).collect(),
        }
    }
    fn ensure(&mut self, si: usize) {
        park_if_dead();
        self.cur = si;
        if self.oracle[si].is_none() {
            self.oracle[si] = Some(
                MaudeHandle::start_with_backend(
                    &self.maude_path,
                    self.sigs[si].sig.clone(),
                    AlgebraBackend::Maude,
                )
                .expect("start Maude oracle"),
            );
        }
        if self.subject[si].is_none() {
            let (path, backend) = match self.cfg {
                Cfg::Native => (MISSING, AlgebraBackend::NativeOnly),
                Cfg::Maude => (self.maude_path.as_str(), AlgebraBackend::Maude),
            };
            self.subject[si] = Some(
                MaudeHandle::start_for_tamarin_theory(
                    path,
                    self.sigs[si].sig.clone(),
                    backend,
                    Default::default(),
                )
                .expect("start subject"),
            );
        }
    }
    fn maude<T>(
        &mut self,
        f: impl FnOnce(&MaudeHandle) -> Result<T, tamarin_term::maude_proc::MaudeError>,
    ) -> Result<T, String> {
        let h = self.oracle[self.cur].as_ref().unwrap();
        f(h).map_err(|e| e.to_string())
    }
    /// Is the tuple `subj` an AC-instance of the tuple `pat`? Subject variables are rigid.
    fn instance(&mut self, subj: &[LNTerm], pat: &[LNTerm]) -> Result<bool, String> {
        let eqs: Vec<Equal<LNTerm>> = subj
            .iter()
            .zip(pat)
            .filter(|(s, p)| !(matches!(p, Term::Lit(Lit::Con(_))) && s == p))
            .map(|(s, p)| {
                let p = canon(
                    &p.clone()
                        .map_free(&mut |x| LVar::new(format!("ZP{}", x.name), x.sort, x.idx)),
                );
                Equal::new(s.clone(), p)
            })
            .collect();
        if eqs.is_empty() {
            return Ok(true);
        }
        self.maude(|h| h.match_eqs(&eqs)).map(|a| !a.is_empty())
    }
}

// -------------------------------------------------------------------- oracles

/// A system variable that an arm leaves unbound stands for itself.
fn rigid(x: &LVar) -> LNTerm {
    let name = format!("SYS{}{}{}", x.name, x.idx, x.sort as u8);
    if x.sort == LSort::Fresh {
        fresh_term(name)
    } else {
        pub_term(name)
    }
}
fn rigid_all(t: &LNTerm) -> LNTerm {
    match t {
        Term::Lit(Lit::Var(x)) => rigid(x),
        Term::Lit(_) => t.clone(),
        Term::App(s, args) => f_app(*s, args.iter().map(rigid_all).collect()),
    }
}
/// Range variables are fresh whatever they are called.
fn fresh_range(t: &LNTerm) -> LNTerm {
    canon(
        &t.clone()
            .map_free(&mut |y| LVar::new(format!("ZR{}", y.name), y.sort, y.idx)),
    )
}
/// Images of one arm over a common variable list.
fn tuple(a: &LNSubstVFresh, universe: &BTreeSet<LVar>) -> Vec<LNTerm> {
    universe
        .iter()
        .map(|d| a.image_of(d).map(fresh_range).unwrap_or_else(|| rigid(d)))
        .collect()
}

type Findings = Vec<(String, String)>;
fn find(out: &mut Findings, class: impl Into<String>, detail: impl Into<String>) {
    let class = class.into();
    if !out.iter().any(|(c, _)| *c == class) {
        out.push((class, detail.into()));
    }
}

/// Checks of one result against the store it came from; no other backend involved.
fn check_step(
    ctx: &mut Ctx,
    out: &mut Findings,
    prefix: &str,
    before: &EquationStore,
    asubst: &LNSubst,
    after: &EquationStore,
) {
    let new_subst = asubst.compose(&before.subst);
    for (d0, d1) in before.conj.iter().zip(&after.conj) {
        // Variables the applied substitution relates to this disjunction.
        let mut related = BTreeSet::new();
        for s in &d0.substs {
            for lv in s.dom() {
                vars_of(&apply_vterm(&new_subst, v(*lv)), &mut related);
            }
        }
        for arm in &d1.substs {
            for (x, t) in arm.iter() {
                if !sort_ok(x.sort, t) {
                    find(
                        out,
                        format!("{prefix}arm-sort-violation"),
                        show_sub(&arm.to_list()),
                    );
                }
                if !related.contains(x) {
                    let mut o = String::from("binds ");
                    show_var(x, &mut o);
                    let _ = write!(o, " in {}", show_sub(&arm.to_list()));
                    find(out, format!("{prefix}arm-binds-unrelated-variable"), o);
                }
            }
            // Some input arm must have this arm as an instance under the new substitution.
            let mp: BTreeMap<LVar, LNTerm> =
                arm.iter().map(|(x, t)| (*x, fresh_range(t))).collect();
            let mut any = d0.substs.is_empty();
            for s in &d0.substs {
                let mut subj = Vec::new();
                let mut pat = Vec::new();
                for (lv, t) in s.iter() {
                    // System variables the arm leaves alone are rigid.
                    let lhs = canon(&apply_vterm(&new_subst, v(*lv)));
                    let mut lv_vars = BTreeSet::new();
                    vars_of(&lhs, &mut lv_vars);
                    let mut m = mp.clone();
                    for y in lv_vars {
                        m.entry(y).or_insert_with(|| rigid(&y));
                    }
                    subj.push(app(&lhs, &m));
                    pat.push(canon(t));
                }
                match ctx.instance(&subj, &pat) {
                    Ok(true) => {
                        any = true;
                        break;
                    }
                    Ok(false) => {}
                    Err(e) => {
                        find(out, "oracle-maude-error", e);
                        any = true;
                        break;
                    }
                }
            }
            if !any {
                find(
                    out,
                    format!("{prefix}arm-not-instance-of-input"),
                    show_sub(&arm.to_list()),
                );
            }
        }
    }
}

/// Differential comparison of two stores up to renaming of fresh range variables.
fn compare(ctx: &mut Ctx, out: &mut Findings, m: &EquationStore, n: &EquationStore) {
    if m.subst != n.subst {
        find(out, "store-free-subst-differs", "");
    }
    if m.conj.len() != n.conj.len()
        || m.conj
            .iter()
            .zip(&n.conj)
            .any(|(a, b)| a.split_id != b.split_id)
    {
        find(
            out,
            "store-disjunctions-differ",
            format!("{} vs {}", m.conj.len(), n.conj.len()),
        );
        return;
    }
    for (dm, dn) in m.conj.iter().zip(&n.conj) {
        if dm.substs.is_empty() != dn.substs.is_empty() {
            find(
                out,
                if dn.substs.is_empty() {
                    "store-subject-false-maude-not"
                } else {
                    "store-maude-false-subject-not"
                },
                format!("split {:?}", dm.split_id),
            );
            continue;
        }
        let mut universe = BTreeSet::new();
        for a in dm.substs.iter().chain(&dn.substs) {
            universe.extend(a.dom().copied());
        }
        let tm: Vec<_> = dm.substs.iter().map(|a| tuple(a, &universe)).collect();
        let tn: Vec<_> = dn.substs.iter().map(|a| tuple(a, &universe)).collect();
        for (xs, ys, arms, class) in [
            (
                &tm,
                &tn,
                &dm.substs,
                "store-INCOMPLETE(maude-arm-not-covered)",
            ),
            (
                &tn,
                &tm,
                &dn.substs,
                "store-subject-arm-not-covered-by-maude",
            ),
        ] {
            for (i, x) in xs.iter().enumerate() {
                let mut covered = false;
                for y in ys.iter() {
                    match ctx.instance(x, y) {
                        Ok(true) => {
                            covered = true;
                            break;
                        }
                        Ok(false) => {}
                        Err(e) => {
                            find(out, "oracle-maude-error", e);
                            covered = true;
                            break;
                        }
                    }
                }
                if !covered {
                    find(
                        out,
                        class,
                        format!(
                            "split {:?} arm {}",
                            dm.split_id,
                            show_sub(&arms[i].to_list())
                        ),
                    );
                }
            }
        }
        if dm.substs.len() != dn.substs.len() {
            find(
                out,
                "info-arm-count-differs",
                format!("maude {} subject {}", dm.substs.len(), dn.substs.len()),
            );
        }
    }
}

struct Run {
    findings: Findings,
    log: String,
}

fn run_case(ctx: &mut Ctx, case: &Case, verbose: bool) -> Run {
    ctx.ensure(case.si);
    let mut findings = Findings::new();
    let mut log = String::new();
    let mut sm = case.store.clone();
    let mut sn = case.store.clone();
    for (k, a) in case.steps.iter().enumerate() {
        let (bm, bn) = (sm.clone(), sn.clone());
        wd_set(format!("step {k} maude"));
        let rm = {
            let h = ctx.oracle[case.si].as_ref().unwrap();
            std::panic::catch_unwind(AssertUnwindSafe(|| sm.apply_eq_store(h, a)))
        };
        wd_set(format!("step {k} subject"));
        let t0 = Instant::now();
        let rn = {
            let h = ctx.subject[case.si].as_ref().unwrap();
            std::panic::catch_unwind(AssertUnwindSafe(|| {
                sn.apply_eq_store(h, a).and_then(|()| {
                    h.check_backend_status().map_err(|e| {
                        tamarin_theory::tools::equation_store::AddEqsError::Maude(e.to_string())
                    })
                })
            }))
        };
        let us = t0.elapsed().as_micros();
        wd_set(format!("step {k} oracles"));
        let flat = |r: std::thread::Result<Result<(), _>>| -> Result<(), String> {
            match r {
                Err(_) => Err("PANIC".into()),
                Ok(Err(e)) => Err(format!("{e}")),
                Ok(Ok(())) => Ok(()),
            }
        };
        let (rm, rn): (Result<(), String>, Result<(), String>) = (flat(rm), flat(rn));
        if verbose {
            let _ = writeln!(log, "--- step {k}: apply {}", show_sub(&a.to_list()));
            let _ = writeln!(
                log,
                "maude {rm:?}:\n{}subject {rn:?} ({us}us):\n{}",
                show_store(&sm),
                show_store(&sn)
            );
        }
        match (&rm, &rn) {
            (Ok(()), Ok(())) => {}
            (Err(e), Ok(())) => {
                find(
                    &mut findings,
                    "maude-error-subject-ok",
                    format!("step {k}: {e}"),
                );
                break;
            }
            (Ok(()), Err(e)) => {
                let t: String = e.chars().take(80).collect();
                find(
                    &mut findings,
                    format!("subject-error: {t}"),
                    format!("step {k}: {e}"),
                );
                ctx.subject[case.si] = None;
                break;
            }
            (Err(_), Err(_)) => break,
        }
        let before = findings.len();
        check_step(ctx, &mut findings, "", &bn, a, &sn);
        check_step(ctx, &mut findings, "maude-", &bm, a, &sm);
        compare(ctx, &mut findings, &sm, &sn);
        if findings.len() > before {
            for f in findings.iter_mut().skip(before) {
                f.1 = format!("step {k}: {}", f.1);
            }
            if findings
                .iter()
                .skip(before)
                .any(|(c, _)| !c.starts_with("info-"))
            {
                break;
            }
        }
    }
    wd_clear();
    Run { findings, log }
}

// -------------------------------------------------------------------- shrinking

fn shrink_cands(c: &Case) -> Vec<Case> {
    let mut out = Vec::new();
    // Fewer steps, last first.
    for i in (0..c.steps.len()).rev() {
        if c.steps.len() > 1 {
            let mut d = c.clone();
            d.steps.remove(i);
            out.push(d);
        }
    }
    // Fewer disjunctions and arms.
    for i in 0..c.store.conj.len() {
        if c.store.conj.len() > 1 {
            let mut d = c.clone();
            d.store.conj.remove(i);
            out.push(d);
        }
        for j in 0..c.store.conj[i].substs.len() {
            if c.store.conj[i].substs.len() > 1 {
                let mut d = c.clone();
                d.store.conj[i].substs.remove(j);
                out.push(d);
            }
        }
    }
    // Fewer bindings.
    for i in 0..c.steps.len() {
        let l = c.steps[i].to_list();
        for j in 0..l.len() {
            let mut l2 = l.clone();
            l2.remove(j);
            let mut d = c.clone();
            d.steps[i] = LNSubst::from_list(l2);
            out.push(d);
        }
    }
    if !c.store.subst.is_empty() {
        let mut d = c.clone();
        d.store.subst = LNSubst::empty();
        out.push(d);
    }
    out
}

fn shrink(ctx: &mut Ctx, c: &Case, class: &str) -> Case {
    let mut cur = c.clone();
    let t0 = Instant::now();
    'outer: loop {
        for d in shrink_cands(&cur) {
            if t0.elapsed() > Duration::from_secs(60) {
                break 'outer;
            }
            ctx.subject[d.si] = None;
            if run_case(ctx, &d, false)
                .findings
                .iter()
                .any(|(k, _)| k == class)
            {
                cur = d;
                continue 'outer;
            }
        }
        break;
    }
    cur
}

// -------------------------------------------------------------------- watchdog, output

static WD: Mutex<Option<(Instant, String)>> = Mutex::new(None);
/// Set by the watchdog before it kills the children; the main thread then stops for good.
static DEAD: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
/// Unix time after which the worker stops (0 = no limit).
static DEADLINE: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
fn dead() -> bool {
    DEAD.load(std::sync::atomic::Ordering::SeqCst)
}
fn park_if_dead() {
    while dead() {
        std::thread::sleep(Duration::from_secs(1));
    }
}
fn now() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}
fn past_deadline() -> bool {
    let d = DEADLINE.load(std::sync::atomic::Ordering::SeqCst);
    d != 0 && now() >= d
}
static OUT: OnceLock<String> = OnceLock::new();
static TIMEOUT: OnceLock<u64> = OnceLock::new();
static WHERE: Mutex<String> = Mutex::new(String::new());

fn wd_set(what: String) {
    park_if_dead();
    *WD.lock().unwrap() = Some((Instant::now(), what));
}
fn wd_clear() {
    *WD.lock().unwrap() = None;
}
fn append(kind: &str, text: &str) {
    match OUT.get() {
        Some(d) => {
            if let Ok(mut f) = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(format!("{d}/{kind}.log"))
            {
                let _ = f.write_all(text.as_bytes());
            }
        }
        None => print!("{text}"),
    }
}
fn kill_children() {
    if let Ok(tasks) = std::fs::read_dir("/proc/self/task") {
        for t in tasks.flatten() {
            if let Ok(s) = std::fs::read_to_string(t.path().join("children")) {
                for pid in s.split_whitespace() {
                    let _ = std::process::Command::new("kill")
                        .args(["-9", pid])
                        .status();
                }
            }
        }
    }
}
fn watchdog() {
    std::thread::spawn(|| loop {
        std::thread::sleep(Duration::from_millis(200));
        let limit = *TIMEOUT.get().unwrap_or(&20);
        let hit = WD
            .lock()
            .unwrap()
            .as_ref()
            // Generation only asks Maude for variants and unifiers of small terms.
            .filter(|(t, w)| {
                t.elapsed()
                    > Duration::from_secs(if w == "generation" {
                        limit.min(4)
                    } else {
                        limit
                    })
            })
            .map(|(_, w)| w.clone());
        if let Some(w) = hit {
            DEAD.store(true, std::sync::atomic::Ordering::SeqCst);
            if w != "generation" {
                append(
                    "hangs",
                    &format!("HANG in {w}: {}\n", WHERE.lock().unwrap()),
                );
            }
            kill_children();
            std::process::exit(if w == "generation" { 4 } else { 3 });
        }
        if past_deadline() {
            DEAD.store(true, std::sync::atomic::Ordering::SeqCst);
            kill_children();
            std::process::exit(5);
        }
    });
}

fn args() -> BTreeMap<String, String> {
    let mut m = BTreeMap::new();
    let a: Vec<String> = std::env::args().skip(2).collect();
    let mut i = 0;
    while i < a.len() {
        if let Some(k) = a[i].strip_prefix("--") {
            let val = a.get(i + 1).filter(|x| !x.starts_with("--")).cloned();
            i += 1 + usize::from(val.is_some());
            m.insert(k.to_owned(), val.unwrap_or_default());
        } else {
            i += 1;
        }
    }
    m
}

fn sig_filter(ctx: &Ctx, a: &BTreeMap<String, String>) -> Vec<usize> {
    match a.get("sigs") {
        Some(s) => s
            .split(',')
            .map(|n| ctx.sigs.iter().position(|x| x.name == n).expect("sig"))
            .collect(),
        None => (0..ctx.sigs.len()).collect(),
    }
}

fn case_for(ctx: &mut Ctx, seed: u64, i: u64, sigs: &[usize]) -> Option<Case> {
    let mut rng = Rng::new(seed ^ i.wrapping_mul(0x9E37_79B9_7F4A_7C15));
    let si = sigs[rng.below(sigs.len())];
    ctx.ensure(si);
    gen_case(&mut rng, ctx, si)
}

fn worker(a: BTreeMap<String, String>) {
    let cfg = Cfg::parse(a.get("cfg").map(String::as_str).unwrap_or("native"));
    let seed: u64 = a.get("seed").and_then(|s| s.parse().ok()).unwrap_or(1);
    let iters: u64 = a.get("iters").and_then(|s| s.parse().ok()).unwrap_or(1000);
    let start: u64 = a.get("start").and_then(|s| s.parse().ok()).unwrap_or(0);
    if let Some(d) = a.get("out") {
        let _ = std::fs::create_dir_all(d);
        let _ = OUT.set(d.clone());
    }
    let _ = TIMEOUT.set(a.get("timeout").and_then(|s| s.parse().ok()).unwrap_or(20));
    watchdog();
    let mut ctx = Ctx::new(cfg);
    let sigs = sig_filter(&ctx, &a);
    let mut stats: BTreeMap<String, u64> = BTreeMap::new();
    let mut seen: BTreeMap<String, u64> = BTreeMap::new();
    if let Some(d) = a.get("deadline").and_then(|s| s.parse().ok()) {
        DEADLINE.store(d, std::sync::atomic::Ordering::SeqCst);
    }
    let write_state = |i: u64, stats: &BTreeMap<String, u64>| {
        if dead() {
            return;
        }
        if let Some(d) = OUT.get() {
            let _ = std::fs::write(format!("{d}/next"), format!("{i}\n"));
            let mut s = String::new();
            for (k, n) in stats {
                let _ = writeln!(s, "{k}\t{n}");
            }
            let _ = std::fs::write(format!("{d}/stats-{start}.tsv"), s);
        }
    };
    for i in start..iters {
        park_if_dead();
        *WHERE.lock().unwrap() = format!("--cfg {} --seed {seed} --iter {i}", cfg.name());
        write_state(i + 1, &stats);
        wd_set("generation".into());
        let Some(case) = case_for(&mut ctx, seed, i, &sigs) else {
            *stats.entry("skipped".into()).or_default() += 1;
            continue;
        };
        let sig = ctx.sigs[case.si].name;
        *stats.entry(format!("cases|{sig}")).or_default() += 1;
        *stats.entry(format!("steps|{sig}")).or_default() += case.steps.len() as u64;
        let run = run_case(&mut ctx, &case, false);
        if run.findings.is_empty() {
            *stats.entry(format!("clean|{sig}")).or_default() += 1;
        }
        for (class, detail) in &run.findings {
            *stats.entry(format!("F|{class}|{sig}")).or_default() += 1;
            let n = seen.entry(format!("{class}|{sig}")).or_default();
            *n += 1;
            if *n > 3 {
                continue;
            }
            let min = if class.starts_with("info-") {
                case.clone()
            } else {
                shrink(&mut ctx, &case, class)
            };
            ctx.subject[min.si] = None;
            let fin = run_case(&mut ctx, &min, true);
            let mut s = String::new();
            let _ = writeln!(
                s,
                "=== FINDING class={class:?} cfg={} sig={sig} occurrence={n}",
                cfg.name()
            );
            let _ = writeln!(s, "detail: {detail}");
            let _ = writeln!(
                s,
                "replay: audit_eqstore_fuzz one --cfg {} --seed {seed} --iter {i}",
                cfg.name()
            );
            let _ = writeln!(
                s,
                "minimized case (measure {} -> {}):\n{}",
                case.measure(),
                min.measure(),
                min.show(sig)
            );
            let _ = writeln!(s, "minimized findings: {:?}", fin.findings);
            let _ = writeln!(s, "{}", fin.log);
            append("findings", &s);
        }
    }
    write_state(iters, &stats);
    drop(ctx);
    kill_children();
}

fn drive(a: BTreeMap<String, String>) {
    let out = a.get("out").cloned().expect("--out DIR");
    let _ = std::fs::create_dir_all(&out);
    let iters: u64 = a.get("iters").and_then(|s| s.parse().ok()).unwrap_or(1000);
    let exe = std::env::current_exe().unwrap();
    let deadline = a
        .get("seconds")
        .and_then(|s| s.parse::<u64>().ok())
        .map(|s| now() + s);
    let mut start = 0u64;
    let mut restarts = 0;
    let mut slow_generation = 0;
    while start < iters && deadline.map_or(true, |d| now() < d) {
        let mut cmd = std::process::Command::new(&exe);
        cmd.arg("worker");
        for (k, val) in &a {
            if k != "start" && k != "seconds" {
                cmd.arg(format!("--{k}")).arg(val);
            }
        }
        cmd.arg("--start").arg(start.to_string());
        if let Some(d) = deadline {
            cmd.arg("--deadline").arg(d.to_string());
        }
        let status = cmd.status().expect("spawn worker");
        let next: u64 = std::fs::read_to_string(format!("{out}/next"))
            .ok()
            .and_then(|s| s.trim().parse().ok())
            .unwrap_or(start + 1);
        if status.success() || status.code() == Some(5) {
            start = next;
            break;
        }
        if status.code() == Some(4) {
            // Maude was slow on a generated term; not a finding about the subject.
            slow_generation += 1;
            start = next.max(start + 1);
            continue;
        }
        restarts += 1;
        let _ = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(format!("{out}/restarts.log"))
            .and_then(|mut f| {
                writeln!(
                    f,
                    "worker exited {status} at iteration {}",
                    next.saturating_sub(1)
                )
            });
        start = next.max(start + 1);
    }
    // Aggregate the per-worker statistics.
    let mut total: BTreeMap<String, u64> = BTreeMap::new();
    if let Ok(rd) = std::fs::read_dir(&out) {
        for e in rd.flatten() {
            let name = e.file_name().to_string_lossy().into_owned();
            if name.starts_with("stats-") {
                for line in std::fs::read_to_string(e.path())
                    .unwrap_or_default()
                    .lines()
                {
                    if let Some((k, n)) = line.split_once('\t') {
                        *total.entry(k.to_owned()).or_default() += n.parse::<u64>().unwrap_or(0);
                    }
                }
            }
        }
    }
    let mut s =
        format!("iterations\t{start}\nrestarts\t{restarts}\nslow-generation\t{slow_generation}\n");
    for (k, n) in &total {
        let _ = writeln!(s, "{k}\t{n}");
    }
    let _ = std::fs::write(format!("{out}/summary.tsv"), &s);
    print!("{s}");
}

fn one(a: BTreeMap<String, String>, t6: bool) {
    let cfg = Cfg::parse(a.get("cfg").map(String::as_str).unwrap_or("native"));
    let _ = TIMEOUT.set(a.get("timeout").and_then(|s| s.parse().ok()).unwrap_or(60));
    watchdog();
    let mut ctx = Ctx::new(cfg);
    let case = if t6 {
        t6_case(&mut ctx)
    } else {
        let seed: u64 = a.get("seed").and_then(|s| s.parse().ok()).unwrap_or(1);
        let i: u64 = a.get("iter").and_then(|s| s.parse().ok()).unwrap_or(0);
        let sigs = sig_filter(&ctx, &a);
        match case_for(&mut ctx, seed, i, &sigs) {
            Some(c) => c,
            None => {
                println!("iteration generates no case");
                return;
            }
        }
    };
    let sig = ctx.sigs[case.si].name;
    println!("{}", case.show(sig));
    let run = run_case(&mut ctx, &case, true);
    println!("{}", run.log);
    println!("findings: {:#?}", run.findings);
    drop(ctx);
    kill_children();
}

fn main() {
    match std::env::args().nth(1).as_deref() {
        Some("drive") => drive(args()),
        Some("worker") => worker(args()),
        Some("one") => one(args(), false),
        Some("t6") => one(args(), true),
        _ => eprintln!("usage: audit_eqstore_fuzz drive|worker|one|t6 ... (see the file header)"),
    }
}
