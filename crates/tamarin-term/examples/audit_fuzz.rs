//! Query-level differential fuzzer: proved-only algebra backend vs Maude.
//!
//! Untracked audit tool. Build (from the tamarin-rs root):
//!   cargo --config 'patch."https://github.com/kmilner/tamarin-algebra.git".tamarin-algebra-sys.path="../tamarin-algebra"' \
//!     build --profile ci -p tamarin-term --features lean-unification --example audit_fuzz
//!
//! Subcommands (binary: target/ci/examples/audit_fuzz):
//!   drive    --cfg native|reference|refvar --seed S --iters N --workers W --out DIR
//!            [--sigs a,b] [--weights u,m,k,r,v]      spawn W workers, restart them after hangs
//!            [--heavy] [--shapes PCT]                wider AC applications; PCT% of the unify and
//!                                                    match queries drawn from the AC shape templates
//!            [--seconds WALL]                        workers stop generating after WALL seconds
//!            [--trace]                               log every generated query (trace-*.log), to
//!                                                    replay a finding that needs the session's history
//!   worker   (internal; same flags plus --wid/--start)
//!   directed --cfg C --out DIR                        run the built-in nasty-case list
//!   one      --cfg C --sig SIG --op unify|unifiable|exists|match|hasmatch|firstmatch|matchsk|reduce|variants
//!            [--shrink] 'QUERY'                       replay one query and print both answers
//!   seq      --cfg C FILE                             replay a trace file's queries in one session
//!   selftest                                          printer/parser round trip
//!
//! Query syntax: terms are `op(args)`; variables `x`, `~x` (Fresh), `$x` (Pub), `%x` (Nat) with an
//! optional `.N` index; public names `'a'`, fresh names `~'n'`. Unify/match queries are
//! `l = r ; l = r` (for match: SUBJECT = PATTERN, the `Equal` order of `match_eqs`); matchsk
//! appends ` @ v1 v2` (bindable pattern variables) and keeps the SUBJECT = PATTERN order in
//! the query text (the call flips it, because `match_eqs_skolemize_both` takes PATTERN =
//! SUBJECT); variants take `t1 ; t2` (packed as a List).
//!
//! Oracles that do not depend on the other backend (run before Maude is consulted, on every
//! configuration, and on Maude's own answers as `maude-*` classes):
//!   * every unifier/matcher is applied to both sides and compared in AC normal form;
//!   * witness scope: a range variable of a unifier that is not a query variable must be
//!     numbered above every query variable. Maude numbers witnesses that way and
//!     `apply_eq_store` relies on it to tell witnesses from system variables.
//! The caller-scope oracle one level up (random `apply_eq_store` calls with bystander system
//! variables) lives in `crates/tamarin-theory/examples/audit_eqstore_fuzz.rs`.
//!
//! The reference configurations are selected by the environment at handle creation, so the
//! driver sets TAM_RS_NATIVE_REFERENCE / TAM_RS_NATIVE_REFERENCE_VARIANTS on its workers; for
//! `one`/`directed` set them yourself to match `--cfg`.
#![allow(clippy::all, clippy::disallowed_macros, dead_code)]

#[cfg(not(feature = "lean-unification"))]
fn main() {
    eprintln!("audit_fuzz needs --features lean-unification");
}

#[cfg(feature = "lean-unification")]
fn main() {
    imp::main()
}

#[cfg(feature = "lean-unification")]
pub(crate) mod imp {
    use std::collections::{BTreeMap, BTreeSet};
    use std::fmt::Write as _;
    use std::io::Write as _;
    use std::panic::AssertUnwindSafe;
    use std::sync::{Mutex, OnceLock};
    use std::time::{Duration, Instant};

    use tamarin_term::algebra_backend::AlgebraBackend;
    use tamarin_term::builtin;
    use tamarin_term::function_symbols::{
        nat_one_sym, AcFctSym, AcSym, CSym, Constructability, FunSym, NdcState, NoEqSym, Privacy,
    };
    use tamarin_term::lterm::{
        fresh_term, pub_term, sort_compare, sort_of_lnterm, HasFrees, LNTerm, LSort, LVar, NameTag,
    };
    use tamarin_term::maude_proc::{MaudeError, MaudeHandle};
    use tamarin_term::maude_sig::{
        asym_enc_maude_sig, hash_maude_sig, pair_maude_sig, signature_maude_sig, sym_enc_maude_sig,
        MaudeSig,
    };
    use tamarin_term::rewriting::{Equal, RRule};
    use tamarin_term::subterm_rule::rrule_to_ctxt_st_rule;
    use tamarin_term::term::{f_app, f_app_ac, f_app_list, f_app_no_eq, Term};
    use tamarin_term::vterm::Lit;
    use tamarin_utils::cancellation::{CancellationGuard, CancellationToken};

    type Sub = Vec<(LVar, LNTerm)>;
    type Eqs = Vec<Equal<LNTerm>>;

    // ---------------------------------------------------------------- rng

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

    // ---------------------------------------------------------------- symbols

    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    enum Op {
        Pair,
        Fst,
        Snd,
        H,
        F,
        G,
        K0,
        K1,
        Union,
        Mult,
        Exp,
        Inv,
        One,
        Dhn,
        Xor,
        Zero,
        Pmult,
        Em,
        Tplus,
        Tone,
        Senc,
        Sdec,
        Aenc,
        Adec,
        Pk,
        Sign,
        Verify,
        True,
        Eqt,
        G0,
        Seal,
        Open,
        Merge,
        Pre,
        C0,
        C1,
        C2,
    }
    use Op::*;
    const ALL_OPS: &[Op] = &[
        Pair, Fst, Snd, H, F, G, K0, K1, Union, Mult, Exp, Inv, One, Dhn, Xor, Zero, Pmult, Em,
        Tplus, Tone, Senc, Sdec, Aenc, Adec, Pk, Sign, Verify, True, Eqt, G0, Seal, Open, Merge,
        Pre, C0, C1, C2,
    ];

    fn user(name: &[u8], arity: usize) -> NoEqSym {
        NoEqSym::new(name, arity, Privacy::Public, Constructability::Constructor)
    }
    fn merge_sym() -> AcFctSym {
        AcFctSym::new(
            b"merge",
            Privacy::Public,
            Constructability::Constructor,
            NdcState::NotNdc,
        )
    }

    impl Op {
        fn name(self) -> &'static str {
            match self {
                Pair => "pair",
                Fst => "fst",
                Snd => "snd",
                H => "h",
                F => "f",
                G => "g",
                K0 => "k0",
                K1 => "k1",
                Union => "union",
                Mult => "mult",
                Exp => "exp",
                Inv => "inv",
                One => "one",
                Dhn => "DH_neutral",
                Xor => "xor",
                Zero => "zero",
                Pmult => "pmult",
                Em => "em",
                Tplus => "tplus",
                Tone => "tone",
                Senc => "senc",
                Sdec => "sdec",
                Aenc => "aenc",
                Adec => "adec",
                Pk => "pk",
                Sign => "sign",
                Verify => "verify",
                True => "true",
                Eqt => "eqt",
                G0 => "g0",
                Seal => "seal",
                Open => "open",
                Merge => "merge",
                Pre => "prefix",
                C0 => "c0",
                C1 => "c1",
                C2 => "c2",
            }
        }
        /// None = AC (two or more arguments).
        fn arity(self) -> Option<usize> {
            Some(match self {
                Union | Mult | Xor | Tplus | Merge => return None,
                K0 | K1 | One | Dhn | Zero | Tone | True => 0,
                Fst | Snd | H | G | Inv | Pk | G0 | Pre | C0 | C1 | C2 => 1,
                Pair | F | Exp | Pmult | Em | Senc | Sdec | Aenc | Adec | Sign | Eqt | Seal => 2,
                Verify | Open => 3,
            })
        }
        fn build(self, mut a: Vec<LNTerm>) -> LNTerm {
            let mut p = || a.remove(0);
            match self {
                Pair => builtin::pair(p(), p()),
                Fst => builtin::fst(p()),
                Snd => builtin::snd(p()),
                H => builtin::hash(p()),
                F => f_app_no_eq(user(b"f", 2), a),
                G => f_app_no_eq(user(b"g", 1), a),
                K0 => f_app_no_eq(user(b"k0", 0), a),
                K1 => f_app_no_eq(user(b"k1", 0), a),
                Union => f_app_ac(AcSym::Union, a),
                Mult => f_app_ac(AcSym::Mult, a),
                Exp => builtin::exp(p(), p()),
                Inv => builtin::inv(p()),
                One => builtin::one_const(),
                Dhn => builtin::dh_neutral(),
                Xor => f_app_ac(AcSym::Xor, a),
                Zero => builtin::zero_const(),
                Pmult => builtin::pmult(p(), p()),
                Em => builtin::emap(p(), p()),
                Tplus => f_app_ac(AcSym::NatPlus, a),
                Tone => f_app_no_eq(nat_one_sym(), a),
                Senc => builtin::senc(p(), p()),
                Sdec => builtin::sdec(p(), p()),
                Aenc => builtin::aenc(p(), p()),
                Adec => builtin::adec(p(), p()),
                Pk => builtin::pk(p()),
                Sign => builtin::sign(p(), p()),
                Verify => builtin::verify(p(), p(), p()),
                True => builtin::true_const(),
                Eqt => f_app_no_eq(user(b"eqt", 2), a),
                G0 => f_app_no_eq(user(b"g0", 1), a),
                Seal => f_app_no_eq(user(b"seal", 2), a),
                Open => f_app_no_eq(user(b"open", 3), a),
                Merge => f_app_ac(AcSym::AcFct(merge_sym()), a),
                Pre => f_app_no_eq(user(b"prefix", 1), a),
                C0 => f_app_no_eq(user(b"c0", 1), a),
                C1 => f_app_no_eq(user(b"c1", 1), a),
                C2 => f_app_no_eq(user(b"c2", 1), a),
            }
        }
    }

    fn op_by_name(s: &str) -> Option<Op> {
        ALL_OPS.iter().copied().find(|o| o.name() == s)
    }

    fn var(name: &str, sort: LSort, idx: u64) -> LNTerm {
        Term::Lit(Lit::Var(LVar::new(name, sort, idx)))
    }
    fn v(x: LVar) -> LNTerm {
        Term::Lit(Lit::Var(x))
    }

    // ---------------------------------------------------------------- signatures

    struct SigInfo {
        name: &'static str,
        sig: MaudeSig,
        /// Symbols that are irreducible at the root.
        cons: Vec<Op>,
        /// Symbols that head some rewrite rule (or cancel under one).
        dest: Vec<Op>,
        has_nat: bool,
        has_ac: bool,
    }

    fn rule(sig: &mut MaudeSig, lhs: LNTerm, rhs: LNTerm) {
        sig.st_rules
            .insert(rrule_to_ctxt_st_rule(&RRule::new(lhs, rhs)).expect("subterm rule"));
    }

    fn base_sig() -> MaudeSig {
        let mut s = pair_maude_sig().merge(hash_maude_sig());
        s.st_fun_syms
            .extend([user(b"f", 2), user(b"g", 1), user(b"k0", 0), user(b"k1", 0)]);
        s.refresh()
    }

    fn user_rules(mut s: MaudeSig) -> MaudeSig {
        s = s
            .merge(sym_enc_maude_sig())
            .merge(asym_enc_maude_sig())
            .merge(signature_maude_sig());
        s.st_fun_syms.extend([
            user(b"eqt", 2),
            user(b"g0", 1),
            user(b"seal", 2),
            user(b"open", 3),
        ]);
        let (x, y, z) = (
            var("x", LSort::Msg, 0),
            var("y", LSort::Msg, 0),
            var("z", LSort::Msg, 0),
        );
        // Non-linear left-hand side with a ground right-hand side.
        rule(
            &mut s,
            Eqt.build(vec![x.clone(), x.clone()]),
            True.build(vec![]),
        );
        // Fully ground rule.
        rule(&mut s, G0.build(vec![K0.build(vec![])]), K1.build(vec![]));
        // Nested constructor under one destructor.
        rule(
            &mut s,
            Open.build(vec![
                Seal.build(vec![Seal.build(vec![x.clone(), y.clone()]), z.clone()]),
                z,
                y,
            ]),
            x,
        );
        s.refresh()
    }

    /// Convergent rules whose right-hand sides are not subterms of their left-hand sides
    /// (`equations [convergent]:`): CBC prefix and a chain of renamings.
    fn conv_rules(mut s: MaudeSig) -> MaudeSig {
        s = s.merge(sym_enc_maude_sig());
        s.st_fun_syms.extend([
            user(b"prefix", 1),
            user(b"c0", 1),
            user(b"c1", 1),
            user(b"c2", 1),
        ]);
        let (x, y, z) = (
            var("x", LSort::Msg, 0),
            var("y", LSort::Msg, 0),
            var("z", LSort::Msg, 0),
        );
        rule(
            &mut s,
            Pre.build(vec![
                Senc.build(vec![Pair.build(vec![x.clone(), y]), z.clone()])
            ]),
            Senc.build(vec![x.clone(), z]),
        );
        rule(&mut s, C0.build(vec![x.clone()]), C1.build(vec![x.clone()]));
        rule(&mut s, C1.build(vec![x.clone()]), C2.build(vec![x]));
        let mut s = s.refresh();
        s.eq_convergent = true;
        s
    }

    const BASE_CONS: &[Op] = &[Pair, H, F, G, K0, K1];
    const BASE_DEST: &[Op] = &[Fst, Snd];
    const USER_CONS: &[Op] = &[Senc, Aenc, Pk, Sign, True, Seal];
    const USER_DEST: &[Op] = &[Sdec, Adec, Verify, Eqt, G0, Open];

    fn sigs() -> Vec<SigInfo> {
        let mk = |name, sig: MaudeSig, cons: &[&[Op]], dest: &[&[Op]]| {
            let cons: Vec<Op> = cons.iter().flat_map(|x| x.iter().copied()).collect();
            let dest: Vec<Op> = dest.iter().flat_map(|x| x.iter().copied()).collect();
            let has_ac = cons
                .iter()
                .chain(&dest)
                .any(|o| o.arity().is_none() || *o == Em);
            SigInfo {
                name,
                has_nat: sig.enable_nat,
                sig: sig.refresh(),
                cons,
                dest,
                has_ac,
            }
        };
        let with = |f: fn(&mut MaudeSig)| {
            let mut s = base_sig();
            f(&mut s);
            s.refresh()
        };
        let mut userac = base_sig();
        userac.st_ac_fun_syms.insert(merge_sym());
        let mut combo = user_rules(base_sig());
        combo.enable_dh = true;
        combo.enable_xor = true;
        combo.enable_mset = true;
        let mut bpx = base_sig();
        bpx.enable_bp = true;
        bpx.enable_xor = true;
        bpx.enable_nat = true;
        vec![
            mk("free", base_sig(), &[BASE_CONS], &[BASE_DEST]),
            mk(
                "mset",
                with(|s| s.enable_mset = true),
                &[BASE_CONS, &[Union]],
                &[BASE_DEST],
            ),
            mk(
                "dh",
                with(|s| s.enable_dh = true),
                &[BASE_CONS, &[Mult, One, Dhn]],
                &[BASE_DEST, &[Exp, Inv]],
            ),
            mk(
                "xor",
                with(|s| s.enable_xor = true),
                &[BASE_CONS, &[Zero]],
                &[BASE_DEST, &[Xor]],
            ),
            mk(
                "bp",
                with(|s| s.enable_bp = true),
                &[BASE_CONS, &[Mult, One, Dhn]],
                &[BASE_DEST, &[Exp, Inv, Pmult, Em]],
            ),
            mk(
                "nat",
                with(|s| s.enable_nat = true),
                &[BASE_CONS, &[Tplus, Tone]],
                &[BASE_DEST],
            ),
            mk(
                "user",
                user_rules(base_sig()),
                &[BASE_CONS, USER_CONS],
                &[BASE_DEST, USER_DEST],
            ),
            mk("userac", userac, &[BASE_CONS, &[Merge]], &[BASE_DEST]),
            mk(
                "combo",
                combo,
                &[BASE_CONS, USER_CONS, &[Mult, One, Dhn, Zero, Union]],
                &[BASE_DEST, USER_DEST, &[Exp, Inv, Xor]],
            ),
            mk(
                "conv",
                conv_rules(base_sig()),
                &[BASE_CONS, &[Senc, C2]],
                &[BASE_DEST, &[Sdec, Pre, C0, C1]],
            ),
            mk(
                "bpxornat",
                bpx,
                &[BASE_CONS, &[Mult, One, Dhn, Zero, Tplus, Tone]],
                &[BASE_DEST, &[Exp, Inv, Pmult, Em, Xor]],
            ),
        ]
    }

    // ---------------------------------------------------------------- term utilities

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

    fn size(t: &LNTerm) -> usize {
        match t {
            Term::Lit(_) => 1,
            Term::App(_, args) => 1 + args.iter().map(size).sum::<usize>(),
        }
    }

    fn vars_of(t: &LNTerm, out: &mut BTreeSet<LVar>) {
        t.for_each_free(&mut |x| {
            out.insert(*x);
        });
    }
    fn var_occ(t: &LNTerm) -> usize {
        let mut n = 0;
        t.for_each_free(&mut |_| n += 1);
        n
    }

    fn well_sorted(t: &LNTerm) -> bool {
        match t {
            Term::Lit(_) => true,
            Term::App(s, args) => {
                args.iter().all(well_sorted)
                    && (*s != FunSym::Ac(AcSym::NatPlus)
                        || args.iter().all(|a| sort_of_lnterm(a) == LSort::Nat))
            }
        }
    }

    fn sort_ok(want: LSort, t: &LNTerm) -> bool {
        matches!(
            sort_compare(sort_of_lnterm(t), want),
            Some(std::cmp::Ordering::Equal | std::cmp::Ordering::Less)
        )
    }

    fn rename_pat(t: &LNTerm) -> LNTerm {
        canon(
            &t.clone()
                .map_free(&mut |x| LVar::new(format!("ZP{}", x.name), x.sort, x.idx)),
        )
    }

    // ---------------------------------------------------------------- printer / parser

    fn show_var(x: &LVar, o: &mut String) {
        o.push_str(match x.sort {
            LSort::Msg => "",
            LSort::Fresh => "~",
            LSort::Pub => "$",
            LSort::Nat => "%",
            LSort::Node => "#",
        });
        o.push_str(x.name);
        if x.idx != 0 {
            let _ = write!(o, ".{}", x.idx);
        }
    }

    fn show_into(t: &LNTerm, o: &mut String) {
        match t {
            Term::Lit(Lit::Var(x)) => show_var(x, o),
            Term::Lit(Lit::Con(n)) => {
                match n.tag {
                    NameTag::Pub => {}
                    NameTag::Fresh => o.push('~'),
                    NameTag::Nat => o.push('%'),
                    NameTag::Node => o.push('#'),
                    NameTag::Abbrev => o.push('?'),
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
    fn show_subs(s: &[Sub]) -> String {
        let mut o = format!("{} answer(s)", s.len());
        for (i, a) in s.iter().enumerate() {
            if i >= 40 {
                o.push_str("\n    ...");
                break;
            }
            let _ = write!(o, "\n    [{}] {}", i, show_sub(a));
        }
        o
    }

    struct P<'a> {
        s: &'a [u8],
        i: usize,
    }
    impl P<'_> {
        fn ws(&mut self) {
            while self.i < self.s.len() && self.s[self.i].is_ascii_whitespace() {
                self.i += 1;
            }
        }
        fn peek(&mut self) -> Option<u8> {
            self.ws();
            self.s.get(self.i).copied()
        }
        fn ident(&mut self) -> Result<String, String> {
            let st = self.i;
            while self.i < self.s.len()
                && (self.s[self.i].is_ascii_alphanumeric() || self.s[self.i] == b'_')
            {
                self.i += 1;
            }
            if st == self.i {
                return Err(format!("identifier expected at byte {st}"));
            }
            Ok(String::from_utf8_lossy(&self.s[st..self.i]).into_owned())
        }
        fn quoted(&mut self) -> Result<String, String> {
            self.i += 1;
            let st = self.i;
            while self.i < self.s.len() && self.s[self.i] != b'\'' {
                self.i += 1;
            }
            if self.i >= self.s.len() {
                return Err("unterminated name".into());
            }
            let r = String::from_utf8_lossy(&self.s[st..self.i]).into_owned();
            self.i += 1;
            Ok(r)
        }
        fn term(&mut self) -> Result<LNTerm, String> {
            let c = self.peek().ok_or("unexpected end")?;
            let sort = match c {
                b'~' => Some(LSort::Fresh),
                b'$' => Some(LSort::Pub),
                b'%' => Some(LSort::Nat),
                _ => None,
            };
            if sort.is_some() {
                self.i += 1;
            }
            if self.s.get(self.i) == Some(&b'\'') {
                let n = self.quoted()?;
                return Ok(match sort {
                    None => pub_term(n),
                    Some(LSort::Fresh) => fresh_term(n),
                    _ => return Err("only public and fresh names are supported".into()),
                });
            }
            let id = self.ident()?;
            if sort.is_none() {
                if let Some(op) = op_by_name(&id) {
                    let mut args = Vec::new();
                    if self.s.get(self.i) == Some(&b'(') {
                        self.i += 1;
                        loop {
                            args.push(self.term()?);
                            match self.peek() {
                                Some(b',') => self.i += 1,
                                Some(b')') => {
                                    self.i += 1;
                                    break;
                                }
                                _ => return Err(format!("',' or ')' expected at byte {}", self.i)),
                            }
                        }
                    }
                    match op.arity() {
                        Some(n) if n != args.len() => {
                            return Err(format!("{} takes {} argument(s)", op.name(), n))
                        }
                        None if args.len() < 2 => {
                            return Err(format!("{} takes two or more arguments", op.name()))
                        }
                        _ => {}
                    }
                    return Ok(op.build(args));
                }
            }
            let mut idx = 0u64;
            if self.s.get(self.i) == Some(&b'.') {
                self.i += 1;
                idx = self.ident()?.parse().map_err(|_| "bad variable index")?;
            }
            Ok(var(&id, sort.unwrap_or(LSort::Msg), idx))
        }
    }
    fn parse_term(s: &str) -> Result<LNTerm, String> {
        let mut p = P {
            s: s.as_bytes(),
            i: 0,
        };
        let t = p.term()?;
        if p.peek().is_some() {
            return Err(format!("trailing input at byte {} in {s:?}", p.i));
        }
        if !well_sorted(&t) {
            return Err(format!("ill-sorted term {s}"));
        }
        Ok(t)
    }

    // ---------------------------------------------------------------- queries

    #[derive(Clone, PartialEq, Eq)]
    enum Q {
        /// sub: 0 = unify, 1 = unifiable then unify, 2 = unifiable alone (replay only).
        Unify(Eqs, u8),
        /// lhs = subject, rhs = pattern. sub: 0 match_eqs, 1 has_match first, 2 first_match first.
        Match(Eqs, u8),
        MatchSk(Eqs, BTreeSet<LVar>),
        Reduce(LNTerm),
        Variants(Vec<LNTerm>),
    }

    impl Q {
        fn op(&self) -> &'static str {
            match self {
                Q::Unify(_, 0) => "unify",
                Q::Unify(_, 2) => "exists",
                Q::Unify(..) => "unifiable",
                Q::Match(_, 0) => "match",
                Q::Match(_, 1) => "hasmatch",
                Q::Match(..) => "firstmatch",
                Q::MatchSk(..) => "matchsk",
                Q::Reduce(_) => "reduce",
                Q::Variants(_) => "variants",
            }
        }
        /// Coarse operation for statistics.
        fn opclass(&self) -> &'static str {
            match self {
                Q::Unify(..) => "unify",
                Q::Match(..) | Q::MatchSk(..) => "match",
                Q::Reduce(_) => "reduce",
                Q::Variants(_) => "variants",
            }
        }
        fn show(&self) -> String {
            let eqs = |e: &Eqs| {
                e.iter()
                    .map(|e| format!("{} = {}", show(&e.lhs), show(&e.rhs)))
                    .collect::<Vec<_>>()
                    .join(" ; ")
            };
            match self {
                Q::Unify(e, _) | Q::Match(e, _) => eqs(e),
                Q::MatchSk(e, b) => {
                    let mut o = eqs(e);
                    o.push_str(" @");
                    for x in b {
                        o.push(' ');
                        show_var(x, &mut o);
                    }
                    o
                }
                Q::Reduce(t) => show(t),
                Q::Variants(ts) => ts.iter().map(show).collect::<Vec<_>>().join(" ; "),
            }
        }
        fn terms(&self) -> Vec<&LNTerm> {
            match self {
                Q::Unify(e, _) | Q::Match(e, _) | Q::MatchSk(e, _) => {
                    e.iter().flat_map(|e| [&e.lhs, &e.rhs]).collect()
                }
                Q::Reduce(t) => vec![t],
                Q::Variants(ts) => ts.iter().collect(),
            }
        }
        fn measure(&self) -> (usize, usize, usize) {
            let ts = self.terms();
            let mut vs = BTreeSet::new();
            ts.iter().for_each(|t| vars_of(t, &mut vs));
            (
                ts.iter().map(|t| size(t)).sum(),
                vs.len(),
                ts.iter().map(|t| var_occ(t)).sum(),
            )
        }
        fn map_terms(&self, f: &mut dyn FnMut(&LNTerm) -> LNTerm) -> Q {
            let eqs = |e: &Eqs, f: &mut dyn FnMut(&LNTerm) -> LNTerm| -> Eqs {
                e.iter().map(|e| Equal::new(f(&e.lhs), f(&e.rhs))).collect()
            };
            match self {
                Q::Unify(e, s) => Q::Unify(eqs(e, f), *s),
                Q::Match(e, s) => Q::Match(eqs(e, f), *s),
                Q::MatchSk(e, b) => Q::MatchSk(eqs(e, f), b.clone()),
                Q::Reduce(t) => Q::Reduce(f(t)),
                Q::Variants(ts) => Q::Variants(ts.iter().map(|t| f(t)).collect()),
            }
        }
    }

    fn parse_query(op: &str, s: &str) -> Result<Q, String> {
        let eqs = |s: &str| -> Result<Eqs, String> {
            s.split(';')
                .map(|e| {
                    let (l, r) = e.split_once('=').ok_or("equation needs '='")?;
                    Ok(Equal::new(parse_term(l.trim())?, parse_term(r.trim())?))
                })
                .collect()
        };
        Ok(match op {
            "unify" => Q::Unify(eqs(s)?, 0),
            "unifiable" => Q::Unify(eqs(s)?, 1),
            "exists" => Q::Unify(eqs(s)?, 2),
            "match" => Q::Match(eqs(s)?, 0),
            "hasmatch" => Q::Match(eqs(s)?, 1),
            "firstmatch" => Q::Match(eqs(s)?, 2),
            "matchsk" => {
                let (e, b) = s.split_once('@').ok_or("matchsk needs '@ vars'")?;
                let mut bind = BTreeSet::new();
                for w in b.split_whitespace() {
                    match parse_term(w)? {
                        Term::Lit(Lit::Var(x)) => bind.insert(x),
                        _ => return Err("bindable list must contain variables".into()),
                    };
                }
                Q::MatchSk(eqs(e)?, bind)
            }
            "reduce" => Q::Reduce(parse_term(s.trim())?),
            "variants" => Q::Variants(
                s.split(';')
                    .map(|t| parse_term(t.trim()))
                    .collect::<Result<_, _>>()?,
            ),
            _ => return Err(format!("unknown op {op}")),
        })
    }

    // ---------------------------------------------------------------- generation

    struct Gen<'a> {
        rng: &'a mut Rng,
        sig: &'a SigInfo,
        vars: Vec<LVar>,
        pool: Vec<LNTerm>,
        /// Percentage of applications that may use a reducible symbol.
        dest_pct: usize,
        /// Wider AC applications with repeated variables.
        heavy: bool,
    }

    impl Gen<'_> {
        fn var_pool(&mut self, names: &[[&str; 4]], lo: usize, hi: usize) -> Vec<LVar> {
            let n = lo + self.rng.below(hi - lo + 1);
            let mut out = Vec::new();
            for _ in 0..n {
                let r = self.rng.below(100);
                let (k, sort) = if r < 58 {
                    (0, LSort::Msg)
                } else if r < 73 {
                    (1, LSort::Fresh)
                } else if r < 86 {
                    (2, LSort::Pub)
                } else if self.sig.has_nat {
                    (3, LSort::Nat)
                } else {
                    (0, LSort::Msg)
                };
                let row = self.rng.below(names.len());
                let name = names[row][k];
                let idx = if self.rng.pct(8) { 1 } else { 0 };
                let x = LVar::new(name, sort, idx);
                if !out.contains(&x) {
                    out.push(x);
                }
            }
            if self.sig.has_nat && self.rng.pct(50) && !out.iter().any(|x| x.sort == LSort::Nat) {
                out.push(LVar::new(names[0][3], LSort::Nat, 0));
            }
            out
        }

        fn const_leaf(&mut self) -> LNTerm {
            let nullary: Vec<Op> = self
                .sig
                .cons
                .iter()
                .copied()
                .filter(|o| o.arity() == Some(0))
                .collect();
            let r = self.rng.below(100);
            if r < 45 {
                pub_term(*self.rng.pick(&["a", "b", "c"]))
            } else if r < 65 {
                fresh_term(*self.rng.pick(&["n", "m"]))
            } else if !nullary.is_empty() {
                self.rng.pick(&nullary).build(vec![])
            } else {
                pub_term("a")
            }
        }

        fn leaf(&mut self) -> LNTerm {
            if !self.vars.is_empty() && self.rng.pct(68) {
                v(*self.rng.pick(&self.vars))
            } else {
                self.const_leaf()
            }
        }

        fn nat(&mut self, depth: usize) -> LNTerm {
            let nv: Vec<LVar> = self
                .vars
                .iter()
                .copied()
                .filter(|x| x.sort == LSort::Nat)
                .collect();
            if depth == 0 || self.rng.pct(55) {
                if !nv.is_empty() && self.rng.pct(70) {
                    v(*self.rng.pick(&nv))
                } else {
                    Tone.build(vec![])
                }
            } else {
                let n = 2 + self.rng.below(2);
                Tplus.build((0..n).map(|_| self.nat(depth - 1)).collect())
            }
        }

        fn of_sort(&mut self, sort: LSort, depth: usize) -> LNTerm {
            let same: Vec<LVar> = self
                .vars
                .iter()
                .copied()
                .filter(|x| x.sort == sort)
                .collect();
            match sort {
                LSort::Nat => self.nat(depth.min(2)),
                LSort::Fresh | LSort::Pub => {
                    if !same.is_empty() && self.rng.pct(50) {
                        v(*self.rng.pick(&same))
                    } else if sort == LSort::Fresh {
                        fresh_term(*self.rng.pick(&["n", "m"]))
                    } else {
                        pub_term(*self.rng.pick(&["a", "b", "c"]))
                    }
                }
                _ => self.term(depth),
            }
        }

        fn term(&mut self, depth: usize) -> LNTerm {
            let r = self.rng.below(100);
            if depth == 0 || r < 28 {
                return self.leaf();
            }
            if r < 40 && !self.pool.is_empty() {
                return self.rng.pick(&self.pool).clone();
            }
            let op = if !self.sig.dest.is_empty() && self.rng.pct(self.dest_pct) {
                *self.rng.pick(&self.sig.dest)
            } else {
                // Bias toward AC and commutative heads where the signature has them.
                let ac: Vec<Op> = self
                    .sig
                    .cons
                    .iter()
                    .chain(&self.sig.dest)
                    .copied()
                    .filter(|o| o.arity().is_none())
                    .collect();
                if !ac.is_empty() && self.rng.pct(35) {
                    *self.rng.pick(&ac)
                } else {
                    *self.rng.pick(&self.sig.cons)
                }
            };
            let t = match op.arity() {
                Some(n) => op.build((0..n).map(|_| self.term(depth - 1)).collect()),
                None if op == Tplus => self.nat(depth.min(2)),
                None => {
                    let n = if self.heavy {
                        2 + self.rng.below(4)
                    } else if self.rng.pct(70) {
                        2
                    } else {
                        3
                    };
                    op.build(
                        (0..n)
                            .map(|_| {
                                if self.rng.pct(if self.heavy { 75 } else { 50 }) {
                                    self.leaf()
                                } else {
                                    self.term(depth - 1)
                                }
                            })
                            .collect(),
                    )
                }
            };
            if self.pool.len() < 8 && size(&t) <= 7 {
                self.pool.push(t.clone());
            }
            t
        }

        fn mutate(&mut self, t: &LNTerm, natctx: bool) -> LNTerm {
            let r = self.rng.below(100);
            match t {
                Term::Lit(_) => {
                    if r < 15 {
                        if natctx {
                            self.nat(0)
                        } else {
                            self.leaf()
                        }
                    } else {
                        t.clone()
                    }
                }
                Term::App(s, args) => {
                    if r < 12 {
                        return if natctx { self.nat(0) } else { self.leaf() };
                    }
                    if r < 18 {
                        return if natctx { self.nat(1) } else { self.term(1) };
                    }
                    let inner_nat = *s == FunSym::Ac(AcSym::NatPlus);
                    let mut a: Vec<LNTerm> =
                        args.iter().map(|x| self.mutate(x, inner_nat)).collect();
                    if matches!(s, FunSym::Ac(_)) && r < 32 {
                        match self.rng.below(3) {
                            0 if a.len() > 2 => {
                                let i = self.rng.below(a.len());
                                a.remove(i);
                            }
                            1 => {
                                let i = self.rng.below(a.len());
                                a.push(a[i].clone());
                            }
                            _ => a.push(if inner_nat { self.nat(0) } else { self.leaf() }),
                        }
                    }
                    f_app(*s, a)
                }
            }
        }

        fn instantiate(&mut self, t: &LNTerm, pct: usize, depth: usize, clash: usize) -> LNTerm {
            let mut vs = BTreeSet::new();
            vars_of(t, &mut vs);
            let mut m = BTreeMap::new();
            for x in vs {
                if self.rng.pct(pct) {
                    let img = if x.sort != LSort::Msg && x.sort != LSort::Nat && self.rng.pct(clash)
                    {
                        self.term(1)
                    } else {
                        let d = self.rng.below(depth + 1);
                        self.of_sort(x.sort, d)
                    };
                    m.insert(x, img);
                }
            }
            app(t, &m)
        }
    }

    const PAT_NAMES: &[[&str; 4]] = &[
        ["x", "a", "p", "n"],
        ["y", "b", "q", "m"],
        ["z", "a", "p", "n"],
        ["w", "b", "q", "m"],
    ];
    const SUBJ_NAMES: &[[&str; 4]] = &[["r", "c", "t", "j"], ["s", "d", "u", "k"]];

    /// Leave gaps below the highest variable index, so that "lowest index the query leaves
    /// unused" and "above every query variable" name a witness differently.
    fn spread_indices(q: &Q, rng: &mut Rng) -> Q {
        let mut off: Vec<((&'static str, LSort), u64)> = Vec::new();
        q.map_terms(&mut |t| {
            canon(&t.clone().map_free(&mut |x| {
                let key = (x.name, x.sort);
                let o = match off.iter().find(|(k, _)| *k == key) {
                    Some((_, o)) => *o,
                    None => {
                        let o = 2 * rng.below(5) as u64;
                        off.push((key, o));
                        o
                    }
                };
                LVar {
                    idx: x.idx + o,
                    ..x
                }
            }))
        })
    }

    /// Unification queries of every signature this fuzzer knows, by the name of the
    /// signature, for the wire tests of `tamarin-term` (`lean_unification/whole/wire_tests.rs`),
    /// which include this file as a module.
    pub(crate) fn wire_samples(
        seed: u64,
        per_sig: usize,
    ) -> Vec<(&'static str, MaudeSig, Vec<Eqs>)> {
        let mut out = Vec::new();
        for (at, si) in sigs().into_iter().enumerate() {
            let mut rng = Rng::new(seed.wrapping_add(at as u64));
            let mut queries = Vec::new();
            while queries.len() < per_sig {
                // Three in ten from the AC shape templates.
                let q = gen_query(&mut rng, &si, &[1, 0, 0, 0, 0], false, 30);
                let q = if rng.pct(50) {
                    spread_indices(&q, &mut rng)
                } else {
                    q
                };
                if let Q::Unify(eqs, _) = q {
                    queries.push(eqs);
                }
            }
            out.push((si.name, si.sig.clone(), queries));
        }
        out
    }

    fn gen_query(
        rng: &mut Rng,
        sig: &SigInfo,
        weights: &[usize; 5],
        heavy: bool,
        shapes: usize,
    ) -> Q {
        let total: usize = weights.iter().sum();
        let mut r = rng.below(total);
        let mut kind = 0;
        for (i, w) in weights.iter().enumerate() {
            if r < *w {
                kind = i;
                break;
            }
            r -= w;
        }
        let limit = if heavy {
            44
        } else if sig.has_ac {
            34
        } else {
            60
        };
        if kind <= 1 && rng.pct(shapes) {
            for _attempt in 0..20 {
                if let Some(q) = gen_shaped(rng, sig, kind) {
                    let q = q.map_terms(&mut |t| canon(t));
                    let q = if kind == 0 && rng.pct(35) {
                        spread_indices(&q, rng)
                    } else {
                        q
                    };
                    if q.measure().0 <= 90 && q.terms().iter().all(|t| well_sorted(t)) {
                        return q;
                    }
                }
            }
        }
        for _attempt in 0..50 {
            let mut g = Gen {
                rng: &mut *rng,
                sig,
                vars: vec![],
                pool: vec![],
                dest_pct: 12,
                heavy: heavy && kind != 4,
            };
            let more = if g.heavy { 2 } else { 0 };
            let depth = match g.rng.below(10) {
                0..=2 => 1,
                3..=6 => 2,
                7..=8 => 3,
                _ => 4,
            };
            let q = match kind {
                0 => {
                    g.vars = g.var_pool(PAT_NAMES, 1 + more, 4 + more);
                    let n = match g.rng.below(20) {
                        0..=11 => 1,
                        12..=16 => 2,
                        17..=18 => 3,
                        _ => 4,
                    };
                    let mut eqs = Vec::new();
                    for _ in 0..n {
                        let lhs = g.term(depth);
                        let rhs = if g.rng.pct(35) {
                            g.term(depth)
                        } else {
                            let inst = g.instantiate(&lhs, 30, 1, 10);
                            g.mutate(&inst, false)
                        };
                        if g.rng.pct(50) {
                            eqs.push(Equal::new(lhs, rhs));
                        } else {
                            eqs.push(Equal::new(rhs, lhs));
                        }
                    }
                    Q::Unify(eqs, if g.rng.pct(25) { 1 } else { 0 })
                }
                1 | 2 => {
                    let pvars = g.var_pool(PAT_NAMES, 1 + more, 4 + more);
                    let svars = if g.rng.pct(30) {
                        let mut s = g.var_pool(PAT_NAMES, 0, 2);
                        s.extend(g.var_pool(SUBJ_NAMES, 0, 2));
                        s
                    } else {
                        g.var_pool(SUBJ_NAMES, 0, 3)
                    };
                    let n = match g.rng.below(10) {
                        0..=6 => 1,
                        7..=8 => 2,
                        _ => 3,
                    };
                    let mut pats = Vec::new();
                    g.vars = pvars.clone();
                    for _ in 0..n {
                        pats.push(g.term(depth));
                    }
                    g.vars = svars.clone();
                    g.pool.clear();
                    // One shared instantiation keeps repeated pattern variables consistent.
                    let mut vs = BTreeSet::new();
                    pats.iter().for_each(|p| vars_of(p, &mut vs));
                    let mut inst = BTreeMap::new();
                    for x in vs {
                        let img = if x.sort != LSort::Msg && x.sort != LSort::Nat && g.rng.pct(10) {
                            g.term(1)
                        } else {
                            let d = g.rng.below(3);
                            g.of_sort(x.sort, d)
                        };
                        inst.insert(x, img);
                    }
                    let mut eqs = Vec::new();
                    for p in pats {
                        let subj = if g.rng.pct(20) {
                            g.term(depth)
                        } else {
                            let s = app(&p, &inst);
                            if g.rng.pct(25) {
                                g.mutate(&s, false)
                            } else {
                                s
                            }
                        };
                        eqs.push(Equal::new(subj, p));
                    }
                    if kind == 1 {
                        Q::Match(eqs, g.rng.below(4).min(2) as u8)
                    } else {
                        let mut sv = BTreeSet::new();
                        eqs.iter().for_each(|e| vars_of(&e.lhs, &mut sv));
                        let bind: BTreeSet<LVar> = pvars
                            .iter()
                            .copied()
                            .filter(|x| !sv.contains(x) && g.rng.pct(85))
                            .collect();
                        Q::MatchSk(eqs, bind)
                    }
                }
                3 => {
                    g.vars = g.var_pool(PAT_NAMES, 0, 3);
                    g.dest_pct = 45;
                    Q::Reduce(g.term(depth.max(2)))
                }
                _ => {
                    g.vars = g.var_pool(PAT_NAMES, 1, if sig.has_ac { 2 } else { 3 });
                    g.dest_pct = 45;
                    let n = match g.rng.below(10) {
                        0..=5 => 1,
                        6..=8 => 2,
                        _ => 3,
                    };
                    let d = if sig.has_ac {
                        depth.min(2)
                    } else {
                        depth.min(3)
                    };
                    Q::Variants((0..n).map(|_| g.term(d)).collect())
                }
            };
            let q = if kind == 0 && rng.pct(45) {
                spread_indices(&q, rng)
            } else {
                q
            };
            let (sz, _, _) = q.measure();
            let lim = if kind == 4 && sig.has_ac { 12 } else { limit };
            if sz <= lim && q.terms().iter().all(|t| well_sorted(t)) {
                return q;
            }
        }
        Q::Reduce(pub_term("a"))
    }

    // ---------------------------------------------------------------- shaped generation

    /// AC shapes that broke the unifier before, which the grammar above reaches only rarely:
    /// rows of variables with coefficients (`p·x + q·y = r·z`), repeated variables under a
    /// product on both sides (`x*x.1 = x*inv(x.1)`), the same AC head nested under pairs on
    /// both sides, free arguments that force each other (`pack(v0,v1)+… = pack(v4,v5)+…`),
    /// one narrow side against a wide one, independent rows, and bags of up to 12 operands.
    struct Shape<'a> {
        rng: &'a mut Rng,
        op: Op,
        nat: bool,
        /// A unary symbol to put around a variable (`inv` under a product, `h` elsewhere).
        wrap: Option<Op>,
        em: bool,
    }

    impl Shape<'_> {
        /// `n` distinct variables with index `idx` or `idx + 1` (`x`, `x.1`).
        fn vars(&mut self, n: usize, idx: u64) -> Vec<LVar> {
            const MSG: &[&str] = &["x", "y", "z", "w", "u", "v"];
            const NAT: &[&str] = &["n", "m", "k", "j", "i", "l"];
            let mut out: Vec<LVar> = Vec::new();
            let mut guard = 0;
            while out.len() < n && guard < 200 {
                guard += 1;
                let r = self.rng.below(100);
                let (name, sort) = if self.nat {
                    (*self.rng.pick(NAT), LSort::Nat)
                } else if r < 78 {
                    (*self.rng.pick(MSG), LSort::Msg)
                } else if r < 89 {
                    (*self.rng.pick(&["a", "b"]), LSort::Fresh)
                } else {
                    (*self.rng.pick(&["p", "q"]), LSort::Pub)
                };
                // Prefer `x`, `x.1` over a new name now and then.
                let x = match out.last() {
                    Some(prev) if self.rng.pct(25) => LVar::new(prev.name, prev.sort, prev.idx + 1),
                    _ => LVar::new(name, sort, idx),
                };
                if !out.contains(&x) {
                    out.push(x);
                }
            }
            out
        }
        fn konst(&mut self) -> LNTerm {
            if self.nat {
                return Tone.build(vec![]);
            }
            match self.rng.below(10) {
                0..=2 => pub_term("a"),
                3..=4 => pub_term("b"),
                5 => pub_term("c"),
                6..=7 => fresh_term("n"),
                8 => H.build(vec![pub_term("a")]),
                _ => K0.build(vec![]),
            }
        }
        fn pack(&mut self, a: LVar, b: LVar) -> LNTerm {
            if self.rng.pct(70) {
                F.build(vec![v(a), v(b)])
            } else {
                Pair.build(vec![v(a), v(b)])
            }
        }
        fn bag(&self, mut items: Vec<LNTerm>) -> LNTerm {
            items.truncate(12);
            if items.len() == 1 {
                items.pop().unwrap()
            } else {
                self.op.build(items)
            }
        }
        /// Each variable repeated one to `maxcoef` times.
        fn row(&mut self, vars: &[LVar], maxcoef: usize) -> Vec<LNTerm> {
            let mut out = Vec::new();
            for x in vars {
                let c = 1 + self.rng.below(maxcoef);
                for _ in 0..c {
                    out.push(v(*x));
                }
            }
            out
        }
        fn small_row(&mut self, vs: &[LVar]) -> Equal<LNTerm> {
            let nl = 1 + self.rng.below(2.min(vs.len()));
            let mut l = Vec::new();
            let mut r = Vec::new();
            for _ in 0..nl + 1 {
                let x = *self.rng.pick(vs);
                l.push(v(x));
            }
            for _ in 0..1 + self.rng.below(3) {
                let x = *self.rng.pick(vs);
                r.push(v(x));
            }
            if self.rng.pct(30) {
                let c = self.konst();
                r.push(c);
            }
            Equal::new(self.bag(l), self.bag(r))
        }

        fn unify(&mut self) -> Eqs {
            let shape = self.rng.below(10);
            match shape {
                // p·x + q·y = r·z: variables only, with coefficients.
                0 | 1 => {
                    let nl = 1 + self.rng.below(3);
                    let nr = 1 + self.rng.below(3);
                    let vs = self.vars(nl + nr, 0);
                    let nl = nl.min(vs.len() - 1).max(1);
                    let maxcoef = if shape == 0 { 4 } else { 2 };
                    let mut l = self.row(&vs[..nl], maxcoef);
                    let mut r = self.row(&vs[nl..], maxcoef);
                    if self.rng.pct(25) {
                        r.push(v(vs[0]));
                    }
                    if self.rng.pct(20) {
                        let c = self.konst();
                        for _ in 0..1 + self.rng.below(2) {
                            l.push(c.clone());
                        }
                    }
                    if l.len() < 2 {
                        l.push(v(vs[0]));
                    }
                    vec![Equal::new(self.bag(l), self.bag(r))]
                }
                // Repeated variables under the head on both sides, some wrapped.
                2 => {
                    let n = 2 + self.rng.below(2);
                    let vs = self.vars(n, 0);
                    if self.rng.pct(30) && vs.len() >= 2 {
                        let w = match self.wrap {
                            Some(w) => w.build(vec![v(vs[1])]),
                            None => v(vs[1]),
                        };
                        return vec![Equal::new(
                            self.bag(vec![v(vs[0]), v(vs[1])]),
                            self.bag(vec![v(vs[0]), w]),
                        )];
                    }
                    let side = |me: &mut Self| {
                        let k = 2 + me.rng.below(3);
                        let items = (0..k)
                            .map(|_| {
                                let x = v(*me.rng.pick(&vs));
                                match me.wrap {
                                    Some(w) if me.rng.pct(35) => w.build(vec![x]),
                                    _ => x,
                                }
                            })
                            .collect();
                        me.bag(items)
                    };
                    let (l, r) = (side(self), side(self));
                    vec![Equal::new(l, r)]
                }
                // The same AC head nested under pairs on both sides.
                3 | 4 => {
                    let n = 3 + self.rng.below(3);
                    let vs = self.vars(n, 0);
                    let small = |me: &mut Self| {
                        if me.rng.pct(15) {
                            return v(*me.rng.pick(&vs));
                        }
                        let k = 2 + me.rng.below(2);
                        let items = (0..k)
                            .map(|_| {
                                if me.rng.pct(78) {
                                    v(*me.rng.pick(&vs))
                                } else {
                                    me.konst()
                                }
                            })
                            .collect();
                        me.bag(items)
                    };
                    let deep = self.rng.pct(30);
                    let free = if !self.nat && self.rng.pct(20) {
                        F
                    } else {
                        Pair
                    };
                    let side = |me: &mut Self| {
                        let (a, b) = (small(me), small(me));
                        if deep {
                            let c = small(me);
                            free.build(vec![a, Pair.build(vec![b, c])])
                        } else {
                            free.build(vec![a, b])
                        }
                    };
                    let (l, r) = (side(self), side(self));
                    vec![Equal::new(l, r)]
                }
                // Free arguments that force each other: pack(v0,v1)+… = pack(v4,v5)+…
                5 if !self.nat => {
                    let n = 6 + self.rng.below(3);
                    let vs = self.vars(n, 0);
                    let side = |me: &mut Self| {
                        let packs = 1 + me.rng.below(2);
                        let mut items = Vec::new();
                        for _ in 0..packs {
                            let (a, b) = (*me.rng.pick(&vs), *me.rng.pick(&vs));
                            items.push(me.pack(a, b));
                        }
                        for _ in 0..1 + me.rng.below(2) {
                            items.push(v(*me.rng.pick(&vs)));
                        }
                        me.bag(items)
                    };
                    let (l, r) = (side(self), side(self));
                    vec![Equal::new(l, r)]
                }
                // A narrow side against a wide one.
                6 => {
                    let nn = 1 + self.rng.below(2);
                    let nw = 1 + self.rng.below(3);
                    let vs = self.vars(nn + nw, 0);
                    let nn = nn.min(vs.len() - 1).max(1);
                    let mut narrow = self.row(&vs[..nn], 2);
                    if narrow.len() < 2 {
                        narrow.push(v(vs[0]));
                    }
                    let k = 4 + self.rng.below(5);
                    let pool: Vec<LNTerm> = (0..3).map(|_| self.konst()).collect();
                    let wide = (0..k)
                        .map(|_| {
                            if self.rng.pct(55) {
                                self.rng.pick(&pool).clone()
                            } else {
                                v(*self.rng.pick(&vs[nn..]))
                            }
                        })
                        .collect();
                    vec![Equal::new(self.bag(narrow), self.bag(wide))]
                }
                // Independent rows: each equation over its own variables.
                7 => {
                    let n = 2 + self.rng.below(3);
                    let mut eqs = Vec::new();
                    for i in 0..n {
                        let k = 2 + self.rng.below(2);
                        let vs = self.vars(k + 2, 3 * i as u64);
                        if self.em && self.rng.pct(50) {
                            eqs.push(Equal::new(
                                Em.build(vec![v(vs[0]), v(vs[1])]),
                                Em.build(vec![v(vs[2]), v(vs[vs.len() - 1])]),
                            ));
                        } else {
                            eqs.push(self.small_row(&vs));
                        }
                    }
                    eqs
                }
                // Large bags: mostly ground operands, a few variables.
                8 => {
                    let n = 7 + self.rng.below(5);
                    let pool: Vec<LNTerm> = (0..5).map(|_| self.konst()).collect();
                    let mut items: Vec<LNTerm> =
                        (0..n).map(|_| self.rng.pick(&pool).clone()).collect();
                    let nv = 2 + self.rng.below(3);
                    let vs = self.vars(nv, 0);
                    let split = 1 + self.rng.below(vs.len() - 1);
                    let mut l = items.clone();
                    for x in &vs[..split] {
                        l.push(v(*x));
                    }
                    l.truncate(12);
                    // The other side: the same operands shuffled, some replaced by variables.
                    for i in (1..items.len()).rev() {
                        let j = self.rng.below(i + 1);
                        items.swap(i, j);
                    }
                    let drop = 1 + self.rng.below(3);
                    items.truncate(items.len().saturating_sub(drop).max(2));
                    for x in &vs[split..] {
                        items.push(v(*x));
                        if self.rng.pct(20) {
                            items.push(v(*x));
                        }
                    }
                    if self.rng.pct(15) {
                        let c = self.konst();
                        items.push(c);
                    }
                    vec![Equal::new(self.bag(l), self.bag(items))]
                }
                // Several rows over one pool of variables.
                _ => {
                    let k = 3 + self.rng.below(2);
                    let vs = self.vars(k, 0);
                    let n = 2 + self.rng.below(2);
                    (0..n).map(|_| self.small_row(&vs)).collect()
                }
            }
        }

        fn ground(&mut self, sort: LSort, subj: &[LVar]) -> LNTerm {
            let same: Vec<LVar> = subj.iter().copied().filter(|x| x.sort == sort).collect();
            if !same.is_empty() && self.rng.pct(20) {
                return v(*self.rng.pick(&same));
            }
            match sort {
                LSort::Fresh => fresh_term(*self.rng.pick(&["n", "m"])),
                LSort::Pub => pub_term(*self.rng.pick(&["a", "b", "c"])),
                LSort::Nat => {
                    if self.rng.pct(60) {
                        Tone.build(vec![])
                    } else {
                        Tplus.build(vec![Tone.build(vec![]), Tone.build(vec![])])
                    }
                }
                _ => {
                    if self.rng.pct(65) {
                        self.konst()
                    } else {
                        let k = 2 + self.rng.below(2);
                        let items = (0..k).map(|_| self.konst()).collect();
                        self.bag(items)
                    }
                }
            }
        }

        /// SUBJECT = PATTERN with a pattern row of variables with coefficients.
        fn matching(&mut self) -> Eqs {
            let n = 1 + self.rng.below(3);
            let pvars = self.vars(n, 0);
            let svars: Vec<LVar> = if self.nat {
                vec![LVar::new("j", LSort::Nat, 7)]
            } else {
                vec![
                    LVar::new("r", LSort::Msg, 7),
                    LVar::new("s", LSort::Msg, 7),
                    LVar::new("c", LSort::Fresh, 7),
                ]
            };
            let mut inst = BTreeMap::new();
            for x in &pvars {
                let g = self.ground(x.sort, &svars);
                inst.insert(*x, g);
            }
            let pattern = |me: &mut Self| {
                let mut items = me.row(&pvars, 3);
                for _ in 0..me.rng.below(3) {
                    let c = me.konst();
                    items.push(c);
                }
                if !me.nat && me.rng.pct(20) {
                    let (a, b) = (*me.rng.pick(&pvars), *me.rng.pick(&pvars));
                    let p = me.pack(a, b);
                    items.push(p);
                }
                if items.len() < 2 {
                    items.push(v(pvars[0]));
                }
                me.bag(items)
            };
            let k = if self.rng.pct(30) { 2 } else { 1 };
            let pats: Vec<LNTerm> = (0..k).map(|_| pattern(self)).collect();
            let mut subjs: Vec<LNTerm> = pats.iter().map(|p| app(p, &inst)).collect();
            if self.rng.pct(25) {
                // An operand more or less: usually no matcher.
                let i = self.rng.below(subjs.len());
                if let Term::App(s, args) = subjs[i].clone() {
                    let mut a: Vec<LNTerm> = args.to_vec();
                    if a.len() > 2 && self.rng.pct(50) {
                        let j = self.rng.below(a.len());
                        a.remove(j);
                    } else if matches!(s, FunSym::Ac(_)) {
                        let c = self.konst();
                        a.push(c);
                    }
                    subjs[i] = f_app(s, a);
                }
            }
            if k == 2 && self.rng.pct(60) {
                // The same AC head under a pair on both sides.
                let p = Pair.build(pats);
                let s = Pair.build(subjs);
                return vec![Equal::new(s, p)];
            }
            subjs
                .into_iter()
                .zip(pats)
                .map(|(s, p)| Equal::new(s, p))
                .collect()
        }
    }

    fn gen_shaped(rng: &mut Rng, sig: &SigInfo, kind: usize) -> Option<Q> {
        let acs: Vec<Op> = sig
            .cons
            .iter()
            .chain(&sig.dest)
            .copied()
            .filter(|o| o.arity().is_none())
            .collect();
        if acs.is_empty() {
            return None;
        }
        let op = *rng.pick(&acs);
        let wrap = if op == Tplus {
            None
        } else if op == Mult && sig.dest.contains(&Inv) {
            Some(Inv)
        } else {
            Some(H)
        };
        let em = sig.dest.contains(&Em);
        let mut s = Shape {
            rng,
            op,
            nat: op == Tplus,
            wrap,
            em,
        };
        Some(if kind == 0 {
            let eqs = s.unify();
            let sub = if s.rng.pct(25) { 1 } else { 0 };
            Q::Unify(eqs, sub)
        } else {
            let eqs = s.matching();
            let sub = s.rng.below(4).min(2) as u8;
            Q::Match(eqs, sub)
        })
    }

    // ---------------------------------------------------------------- shrinking

    fn term_cands(t: &LNTerm, out: &mut Vec<LNTerm>) {
        if let Term::App(s, args) = t {
            for a in args.iter() {
                out.push(a.clone());
            }
            out.push(pub_term("a"));
            if matches!(s, FunSym::Ac(_)) && args.len() > 2 {
                for i in 0..args.len() {
                    let mut a: Vec<LNTerm> = args.to_vec();
                    a.remove(i);
                    out.push(f_app(*s, a));
                }
            }
            for i in 0..args.len() {
                let mut sub = Vec::new();
                term_cands(&args[i], &mut sub);
                for c in sub {
                    let mut a: Vec<LNTerm> = args.to_vec();
                    a[i] = c;
                    out.push(f_app(*s, a));
                }
            }
        }
    }

    fn query_cands(q: &Q) -> Vec<Q> {
        let mut out = Vec::new();
        let eq_cands = |e: &Eqs, mk: &dyn Fn(Eqs) -> Q, out: &mut Vec<Q>| {
            if e.len() > 1 {
                for i in 0..e.len() {
                    let mut c = e.clone();
                    c.remove(i);
                    out.push(mk(c));
                }
            }
            for i in 0..e.len() {
                for side in 0..2 {
                    let mut cs = Vec::new();
                    term_cands(if side == 0 { &e[i].lhs } else { &e[i].rhs }, &mut cs);
                    for c in cs {
                        let mut n = e.clone();
                        if side == 0 {
                            n[i].lhs = c;
                        } else {
                            n[i].rhs = c;
                        }
                        out.push(mk(n));
                    }
                }
            }
        };
        match q {
            Q::Unify(e, s) => eq_cands(e, &|e| Q::Unify(e, *s), &mut out),
            Q::Match(e, s) => eq_cands(e, &|e| Q::Match(e, *s), &mut out),
            Q::MatchSk(e, b) => eq_cands(e, &|e| Q::MatchSk(e, b.clone()), &mut out),
            Q::Reduce(t) => {
                let mut cs = Vec::new();
                term_cands(t, &mut cs);
                out.extend(cs.into_iter().map(Q::Reduce));
            }
            Q::Variants(ts) => {
                if ts.len() > 1 {
                    for i in 0..ts.len() {
                        let mut c = ts.clone();
                        c.remove(i);
                        out.push(Q::Variants(c));
                    }
                }
                for i in 0..ts.len() {
                    let mut cs = Vec::new();
                    term_cands(&ts[i], &mut cs);
                    for c in cs {
                        let mut n = ts.clone();
                        n[i] = c;
                        out.push(Q::Variants(n));
                    }
                }
            }
        }
        // Merge two variables of one sort, or replace a variable by a constant.
        let mut vs = BTreeSet::new();
        q.terms().iter().for_each(|t| vars_of(t, &mut vs));
        let vs: Vec<LVar> = vs.into_iter().collect();
        for (i, a) in vs.iter().enumerate() {
            for b in &vs[i + 1..] {
                if a.sort == b.sort {
                    let m: BTreeMap<LVar, LNTerm> = [(*b, v(*a))].into();
                    out.push(q.map_terms(&mut |t| app(t, &m)));
                }
            }
            if a.sort == LSort::Msg || a.sort == LSort::Pub {
                let m: BTreeMap<LVar, LNTerm> = [(*a, pub_term("a"))].into();
                out.push(q.map_terms(&mut |t| app(t, &m)));
            }
        }
        let base = q.measure();
        out.retain(|c| c.measure() < base && c.terms().iter().all(|t| well_sorted(t)));
        out.retain(|c| match c {
            Q::MatchSk(e, b) => {
                let mut sv = BTreeSet::new();
                e.iter().for_each(|e| vars_of(&e.lhs, &mut sv));
                !b.iter().any(|x| sv.contains(x))
            }
            _ => true,
        });
        out.sort_by_key(|c| c.measure());
        out.dedup_by(|a, b| a == b);
        out
    }

    // ---------------------------------------------------------------- watchdog and stats

    struct Wd {
        phase: u8,
        start: Instant,
        query: String,
        token: Option<CancellationToken>,
        cancel_sent: bool,
        killed: bool,
    }
    static WD: Mutex<Option<Wd>> = Mutex::new(None);
    static STATS: Mutex<BTreeMap<String, u64>> = Mutex::new(BTreeMap::new());
    static MAXLAT: Mutex<BTreeMap<String, (u64, String)>> = Mutex::new(BTreeMap::new());
    static OUT: OnceLock<(String, String)> = OnceLock::new(); // (dir, tag)
    static META: Mutex<String> = Mutex::new(String::new());
    static LIMITS: OnceLock<(u64, u64, u64, u64)> = OnceLock::new(); // soft, hard, maude, rss_mb

    fn st(key: &str) {
        *STATS.lock().unwrap().entry(key.to_owned()).or_insert(0) += 1;
    }
    fn st_add(key: &str, n: u64) {
        *STATS.lock().unwrap().entry(key.to_owned()).or_insert(0) += n;
    }

    fn out_path(kind: &str, ext: &str) -> Option<String> {
        OUT.get().map(|(d, t)| format!("{d}/{kind}-{t}.{ext}"))
    }
    fn append(kind: &str, text: &str) {
        match out_path(kind, "log") {
            Some(p) => {
                if let Ok(mut f) = std::fs::OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(p)
                {
                    let _ = f.write_all(text.as_bytes());
                }
            }
            None => print!("{text}"),
        }
    }
    fn flush_stats(suffix: &str) {
        let Some((d, t)) = OUT.get() else { return };
        let mut s = String::new();
        for (k, n) in STATS.lock().unwrap().iter() {
            let _ = writeln!(s, "{k}\t{n}");
        }
        let _ = std::fs::write(format!("{d}/stats-{t}-{suffix}.tsv"), s);
        let mut s = String::new();
        for (k, (us, q)) in MAXLAT.lock().unwrap().iter() {
            let _ = writeln!(s, "{k}\t{us}\t{q}");
        }
        let _ = std::fs::write(format!("{d}/maxlat-{t}-{suffix}.tsv"), s);
    }
    static SUFFIX: OnceLock<String> = OnceLock::new();

    fn children() -> Vec<String> {
        let mut out = Vec::new();
        if let Ok(tasks) = std::fs::read_dir("/proc/self/task") {
            for t in tasks.flatten() {
                if let Ok(s) = std::fs::read_to_string(t.path().join("children")) {
                    out.extend(s.split_whitespace().map(str::to_owned));
                }
            }
        }
        out
    }
    fn kill_children() {
        for pid in children() {
            let _ = std::process::Command::new("kill")
                .args(["-9", &pid])
                .status();
        }
    }
    fn rss_mb(pid: &str) -> u64 {
        std::fs::read_to_string(format!("/proc/{pid}/statm"))
            .ok()
            .and_then(|s| {
                s.split_whitespace()
                    .nth(1)
                    .and_then(|x| x.parse::<u64>().ok())
            })
            .map_or(0, |pages| pages * 4096 / (1 << 20))
    }

    fn die(code: i32, what: &str, query: &str) -> ! {
        append(
            "findings",
            &format!(
                "=== FATAL {what} {}\nquery: {query}\n\n",
                META.lock().unwrap()
            ),
        );
        st(&format!("FATAL|{what}"));
        flush_stats(SUFFIX.get().map_or("x", |s| s.as_str()));
        kill_children();
        std::process::exit(code);
    }

    fn watchdog() {
        let (soft, hard, maude, rss) = *LIMITS.get().unwrap();
        let mut tick = 0u64;
        loop {
            std::thread::sleep(Duration::from_millis(100));
            tick += 1;
            {
                let mut g = WD.lock().unwrap();
                if let Some(w) = g.as_mut() {
                    let el = w.start.elapsed().as_millis() as u64;
                    if w.phase == 1 {
                        if el > soft && !w.cancel_sent {
                            w.cancel_sent = true;
                            if let Some(t) = &w.token {
                                t.request_cancel();
                            }
                        }
                        if el > hard {
                            let q = w.query.clone();
                            drop(g);
                            die(3, "NATIVE-HANG(no response to cancellation)", &q);
                        }
                    } else if w.phase == 2 && el > maude && !w.killed {
                        w.killed = true;
                        drop(g);
                        kill_children();
                    }
                }
            }
            if tick % 10 == 0 {
                if rss_mb("self") > rss {
                    let q = WD
                        .lock()
                        .unwrap()
                        .as_ref()
                        .map_or(String::new(), |w| w.query.clone());
                    die(5, "NATIVE-MEMORY", &q);
                }
                if children().iter().any(|c| rss_mb(c) > rss) {
                    kill_children();
                }
            }
        }
    }

    fn wd_set(phase: u8, q: &str, token: Option<CancellationToken>) {
        *WD.lock().unwrap() = Some(Wd {
            phase,
            start: Instant::now(),
            query: if phase == 0 {
                String::new()
            } else {
                q.to_owned()
            },
            token,
            cancel_sent: false,
            killed: false,
        });
    }
    /// Returns whether the watchdog intervened (cancellation or kill).
    fn wd_clear() -> bool {
        let mut g = WD.lock().unwrap();
        let hit = g.as_ref().is_some_and(|w| w.cancel_sent || w.killed);
        if let Some(w) = g.as_mut() {
            w.phase = 0;
        }
        hit
    }

    // ---------------------------------------------------------------- backends

    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    enum Cfg {
        Native,
        Reference,
        RefVar,
    }
    impl Cfg {
        fn parse(s: &str) -> Cfg {
            match s {
                "native" => Cfg::Native,
                "reference" => Cfg::Reference,
                "refvar" => Cfg::RefVar,
                _ => panic!("unknown cfg {s}"),
            }
        }
        fn name(self) -> &'static str {
            match self {
                Cfg::Native => "native",
                Cfg::Reference => "reference",
                Cfg::RefVar => "refvar",
            }
        }
        fn env(self) -> Vec<(&'static str, &'static str)> {
            match self {
                Cfg::Reference => vec![("TAM_RS_NATIVE_REFERENCE", "1")],
                Cfg::RefVar => vec![("TAM_RS_NATIVE_REFERENCE_VARIANTS", "1")],
                _ => vec![],
            }
        }
        fn check_env(self) {
            let r = std::env::var("TAM_RS_NATIVE_REFERENCE").ok().as_deref() == Some("1");
            let rv = std::env::var("TAM_RS_NATIVE_REFERENCE_VARIANTS")
                .ok()
                .as_deref()
                == Some("1");
            let want = (self == Cfg::Reference, self == Cfg::RefVar);
            assert_eq!(
                (r, rv),
                want,
                "environment does not match --cfg {}: set/unset TAM_RS_NATIVE_REFERENCE[_VARIANTS]",
                self.name()
            );
        }
    }

    struct Ctx {
        cfg: Cfg,
        maude_path: String,
        sigs: Vec<SigInfo>,
        oracle: Vec<Option<MaudeHandle>>,
        subject: Vec<Option<MaudeHandle>>,
        /// Use a protocol-theory session (`start_for_tamarin_theory`).
        theory: bool,
        /// Skip the subject backend (time Maude on a query that hangs natively).
        maude_only: bool,
    }

    const MISSING: &str = "/nonexistent/audit-fuzz-proved-only-must-not-start-maude";

    impl Ctx {
        fn new(cfg: Cfg, theory: bool) -> Ctx {
            cfg.check_env();
            let sigs = sigs();
            let n = sigs.len();
            Ctx {
                cfg,
                maude_path: tamarin_test_support::maude_path().unwrap_or_else(|| "maude".into()),
                sigs,
                oracle: (0..n).map(|_| None).collect(),
                subject: (0..n).map(|_| None).collect(),
                theory,
                maude_only: false,
            }
        }
        fn sig_index(&self, name: &str) -> usize {
            self.sigs
                .iter()
                .position(|s| s.name == name)
                .unwrap_or_else(|| panic!("unknown sig {name}"))
        }
        fn ensure(&mut self, si: usize) {
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
                let (path, backend) = (MISSING, AlgebraBackend::ProvedOnly);
                let sig = self.sigs[si].sig.clone();
                self.subject[si] = Some(if self.theory {
                    MaudeHandle::start_for_tamarin_theory(path, sig, backend, Default::default())
                        .expect("start subject")
                } else {
                    MaudeHandle::start_with_backend(path, sig, backend).expect("start subject")
                });
            }
        }
        fn fresh_subject(&mut self, si: usize) {
            self.subject[si] = None;
        }

        fn native<T>(
            &mut self,
            si: usize,
            q: &str,
            f: impl FnOnce(&MaudeHandle) -> Result<T, MaudeError>,
        ) -> (Result<T, String>, u64) {
            if self.maude_only {
                return (Err("skipped (--maude-only)".into()), 0);
            }
            self.ensure(si);
            let token = CancellationToken::default();
            wd_set(1, q, Some(token.clone()));
            let h = self.subject[si].as_ref().unwrap();
            let t0 = Instant::now();
            let r = {
                let _g = CancellationGuard::new(Some(token));
                std::panic::catch_unwind(AssertUnwindSafe(|| f(h)))
            };
            let us = t0.elapsed().as_micros() as u64;
            let hit = wd_clear();
            let r = match r {
                Err(p) => Err(format!(
                    "PANIC: {}",
                    p.downcast_ref::<String>()
                        .cloned()
                        .or_else(|| p.downcast_ref::<&str>().map(|s| (*s).to_owned()))
                        .unwrap_or_default()
                )),
                Ok(Err(e)) => Err(e.to_string()),
                Ok(Ok(x)) => match h.check_backend_status() {
                    Ok(()) => Ok(x),
                    Err(e) => Err(format!("latched after Ok: {e}")),
                },
            };
            let r = r.map_err(|e| {
                if hit {
                    format!("TIMEOUT({us}us): {e}")
                } else {
                    e
                }
            });
            if r.is_err() {
                self.subject[si] = None;
            }
            (r, us)
        }

        fn maude<T>(
            &mut self,
            si: usize,
            q: &str,
            f: impl FnOnce(&MaudeHandle) -> Result<T, MaudeError>,
        ) -> (Result<T, String>, u64) {
            self.ensure(si);
            wd_set(2, q, None);
            let h = self.oracle[si].as_ref().unwrap();
            let t0 = Instant::now();
            let r = std::panic::catch_unwind(AssertUnwindSafe(|| f(h)));
            let us = t0.elapsed().as_micros() as u64;
            let hit = wd_clear();
            let r = match r {
                Err(_) => Err("PANIC in Maude path".to_owned()),
                Ok(Err(e)) => Err(e.to_string()),
                Ok(Ok(x)) => Ok(x),
            };
            let r = r.map_err(|e| {
                if hit {
                    format!("TIMEOUT({us}us): {e}")
                } else {
                    e
                }
            });
            if r.is_err() {
                // The watchdog kills every child, so no handle survives.
                self.oracle.iter_mut().for_each(|h| *h = None);
                self.subject.iter_mut().for_each(|h| *h = None);
            }
            (r, us)
        }

        /// Is the tuple `subj` an instance (modulo the attributes) of the tuple `pat`?
        fn instance(&mut self, si: usize, subj: &[LNTerm], pat: &[LNTerm]) -> Result<bool, String> {
            let eqs: Eqs = subj
                .iter()
                .zip(pat)
                .filter(|(s, p)| !(matches!(p, Term::Lit(Lit::Con(_))) && s == p))
                .map(|(s, p)| Equal::new(s.clone(), rename_pat(p)))
                .collect();
            if eqs.is_empty() {
                return Ok(true);
            }
            st("oracle|instance-checks");
            self.maude(si, "<instance check>", |h| h.match_eqs(&eqs))
                .0
                .map(|a| !a.is_empty())
        }

        /// Indices of `xs` that are not an instance of any element of `ys`.
        fn uncovered(
            &mut self,
            si: usize,
            xs: &[Vec<LNTerm>],
            ys: &[Vec<LNTerm>],
        ) -> Result<Vec<usize>, String> {
            let mut out = Vec::new();
            let cap = if xs.len() * ys.len() > 900 {
                12
            } else {
                usize::MAX
            };
            for (i, x) in xs.iter().enumerate().take(cap) {
                let mut found = false;
                // The aligned index first, then the rest.
                let order = (i..ys.len().min(i + 1)).chain((0..ys.len()).filter(|j| *j != i));
                for j in order {
                    if self.instance(si, x, &ys[j])? {
                        found = true;
                        break;
                    }
                }
                if !found {
                    out.push(i);
                }
            }
            Ok(out)
        }
    }

    // ---------------------------------------------------------------- evaluation

    #[derive(Default)]
    struct Out {
        findings: Vec<(String, String)>,
        native: String,
        maude: String,
        native_us: u64,
        maude_us: u64,
        n_native: usize,
        n_maude: usize,
        /// How the native listing compares with Maude's as written: "same", "permuted"
        /// (the same answers in another order) or "different" (other witness names, another
        /// complete set). Not an oracle; the prover's output order follows the listing.
        listing: Option<&'static str>,
    }

    fn listing(n: &[Sub], m: &[Sub]) -> &'static str {
        // A binding to a variable of the same sort that occurs nowhere else in the answer
        // only renames: Maude spells the identity out, the native paths may leave it empty.
        let norm = |xs: &[Sub]| -> Vec<Vec<(LVar, LNTerm)>> {
            xs.iter()
                .map(|a| {
                    let mut occ: BTreeMap<LVar, usize> = BTreeMap::new();
                    for (_, t) in a {
                        t.for_each_free(&mut |y| *occ.entry(*y).or_insert(0) += 1);
                    }
                    let mut a: Vec<(LVar, LNTerm)> = a
                        .iter()
                        .filter(|(x, t)| {
                            !matches!(t, Term::Lit(Lit::Var(y))
                                if y.sort == x.sort && occ.get(y) == Some(&1))
                        })
                        .map(|(x, t)| (*x, canon(t)))
                        .collect();
                    a.sort();
                    a
                })
                .collect()
        };
        let (mut n, mut m) = (norm(n), norm(m));
        if n == m {
            return "same";
        }
        n.sort();
        m.sort();
        if n == m {
            "permuted"
        } else {
            "different"
        }
    }
    impl Out {
        fn find(&mut self, class: impl Into<String>, detail: impl Into<String>) {
            let class = class.into();
            if !self.findings.iter().any(|(c, _)| *c == class) {
                self.findings.push((class, detail.into()));
            }
        }
        fn native_err(&mut self, what: &str, e: &str) {
            let class = if e.starts_with("TIMEOUT") {
                format!("native-timeout[{what}]")
            } else {
                let mut t: String = e.chars().take(90).collect();
                t = t.replace('\n', " ");
                format!("native-error[{what}]: {t}")
            };
            self.native = format!("ERROR {e}");
            self.find(class, e);
        }
    }

    fn images(a: &Sub, vars: &BTreeSet<LVar>) -> Vec<LNTerm> {
        let m: BTreeMap<LVar, LNTerm> = a.iter().cloned().collect();
        vars.iter()
            .map(|x| m.get(x).map(canon).unwrap_or_else(|| v(*x)))
            .collect()
    }

    /// Unifiers and variant substitutions have a fresh range (`SubstVFresh`): a range variable
    /// that happens to share its identity with a query variable is still a different variable.
    fn freshen(a: &Sub) -> Sub {
        a.iter()
            .map(|(x, t)| {
                (
                    *x,
                    canon(
                        &t.clone()
                            .map_free(&mut |y| LVar::new(format!("ZR{}", y.name), y.sort, y.idx)),
                    ),
                )
            })
            .collect()
    }

    /// Witness scope of one unifier: every range variable that is not a query variable must be
    /// numbered strictly above the highest query variable. A witness below that bound can
    /// share its identity with a caller variable that merely did not occur in this query.
    fn witness_scope(a: &Sub, qvars: &BTreeSet<LVar>) -> Option<String> {
        let top = qvars.iter().map(|x| x.idx).max()?;
        let mut low = BTreeSet::new();
        for (_, t) in a {
            t.for_each_free(&mut |y| {
                if !qvars.contains(y) && y.idx <= top {
                    low.insert(*y);
                }
            });
        }
        if low.is_empty() {
            return None;
        }
        let mut o = String::from("witness(es)");
        for y in &low {
            o.push(' ');
            show_var(y, &mut o);
        }
        let _ = write!(
            o,
            " not above the highest query index {top} in {}",
            show_sub(a)
        );
        Some(o)
    }

    /// Well-formedness shared by unifiers, matchers and variant substitutions.
    fn check_subst(out: &mut Out, kind: &str, a: &Sub, qvars: &BTreeSet<LVar>, fresh_range: bool) {
        let m: BTreeMap<LVar, LNTerm> = a.iter().cloned().collect();
        if m.len() != a.len() {
            out.find(format!("{kind}-duplicate-binding"), show_sub(a));
        }
        for (x, t) in a {
            if !sort_ok(x.sort, t) {
                out.find(format!("{kind}-sort-violation"), show_sub(a));
            }
            if !qvars.contains(x) {
                out.find(format!("{kind}-binds-foreign-variable"), show_sub(a));
            }
            if fresh_range {
                let mut r = BTreeSet::new();
                vars_of(t, &mut r);
                let identity = matches!(t, Term::Lit(Lit::Var(y)) if y == x);
                if !identity && r.iter().any(|y| m.contains_key(y)) {
                    out.find(format!("{kind}-not-idempotent"), show_sub(a));
                } else if !identity && r.iter().any(|y| qvars.contains(y)) {
                    out.find(format!("{kind}-range-reuses-query-variable"), show_sub(a));
                }
            }
        }
    }

    fn eval(ctx: &mut Ctx, si: usize, q: &Q, full: bool) -> Out {
        let qs = q.show();
        let mut out = Out::default();
        match q {
            Q::Unify(eqs, sub) => {
                let mut qvars = BTreeSet::new();
                q.terms().iter().for_each(|t| vars_of(t, &mut qvars));
                let mut pre = None;
                if *sub >= 1 {
                    let (r, t) = ctx.native(si, &qs, |h| h.unifiable(eqs));
                    if *sub == 2 {
                        out.native_us = t;
                        out.native = format!("unifiable = {r:?}");
                    }
                    match r {
                        Ok(b) => pre = Some(b),
                        Err(e) => {
                            out.native_err("unifiable", &e);
                            if !full {
                                return out;
                            }
                        }
                    }
                }
                let (rn, tn) = if *sub == 2 {
                    (Err("existence only".to_owned()), out.native_us)
                } else {
                    ctx.native(si, &qs, |h| h.unify(eqs))
                };
                out.native_us = tn;
                if let (Err(e), true) = (&rn, *sub != 2) {
                    out.native_err("unify", e);
                    if !full {
                        return out;
                    }
                }
                // Checked against the query alone, before the other backend is consulted.
                let sound = |a: &Sub| {
                    let mp: BTreeMap<LVar, LNTerm> = a.iter().cloned().collect();
                    eqs.iter().all(|e| app(&e.lhs, &mp) == app(&e.rhs, &mp))
                };
                let mut n_sound = Vec::new();
                if let Ok(n) = &rn {
                    out.native = show_subs(n);
                    out.n_native = n.len();
                    for (i, a) in n.iter().enumerate() {
                        check_subst(&mut out, "unify", a, &qvars, true);
                        if let Some(d) = witness_scope(a, &qvars) {
                            out.find("unify-witness-not-above-query", d);
                        }
                        let ok = sound(&freshen(a));
                        n_sound.push(ok);
                        if !ok {
                            out.find("unify-UNSOUND", format!("answer [{i}] {}", show_sub(a)));
                        }
                    }
                }
                let (rm, tm) = ctx.maude(si, &qs, |h| h.unify(eqs));
                out.maude_us = tm;
                let m = match rm {
                    Ok(m) => m,
                    Err(e) => {
                        out.maude = format!("ERROR {e}");
                        out.find(maude_err_class(&e), e);
                        return out;
                    }
                };
                out.maude = show_subs(&m);
                out.n_maude = m.len();
                if let Some(b) = pre {
                    if b == m.is_empty() {
                        // Ask a session that has answered nothing yet: a different reply
                        // means the wrong one came from what the session had stored.
                        ctx.fresh_subject(si);
                        let again = ctx.native(si, &qs, |h| h.unifiable(eqs)).0;
                        let class = match again {
                            Ok(b2) if b2 != b => "unifiable-MISMATCH(session-dependent)",
                            _ => "unifiable-MISMATCH",
                        };
                        out.find(
                            class,
                            format!("native unifiable={b}, Maude has {} unifier(s)", m.len()),
                        );
                    }
                }
                let mut maude_reuses = false;
                for a in &m {
                    let mut probe = Out::default();
                    check_subst(&mut probe, "unify", a, &qvars, true);
                    for (c, _) in probe.findings {
                        // A Maude witness that is spelled exactly like a query variable
                        // is as low as one below the bound; `witness_scope` cannot see it.
                        maude_reuses |= c == "unify-range-reuses-query-variable";
                        st(&format!("maude-side|{c}"));
                    }
                    // Maude numbers above the residual it was sent, not above the whole
                    // query, so this is a class of its own.
                    if let Some(d) = witness_scope(a, &qvars) {
                        out.find("maude-witness-not-above-query", d);
                    }
                }
                // Maude's own answers break the numbering rule on some queries (see above);
                // a native answer that breaks it where Maude's do not is a class of its own.
                if let Some(d) = out
                    .findings
                    .iter()
                    .find(|(c, _)| c == "unify-witness-not-above-query")
                    .map(|(_, d)| d.clone())
                {
                    if !maude_reuses
                        && !out
                            .findings
                            .iter()
                            .any(|(c, _)| c == "maude-witness-not-above-query")
                    {
                        out.find("unify-witness-not-above-query(proved-only)", d);
                    }
                }
                if let Ok(n) = &rn {
                    out.listing = Some(listing(n, &m));
                }
                let m: Vec<Sub> = m.iter().map(freshen).collect();
                let Ok(n) = rn else { return out };
                let n: Vec<Sub> = n.iter().map(freshen).collect();
                for a in &m {
                    if !sound(a) {
                        out.find("oracle-maude-unsound-unifier", show_sub(a));
                    }
                }
                if n.is_empty() != m.is_empty() {
                    out.find(
                        if n.is_empty() {
                            "unify-INCOMPLETE-EMPTY"
                        } else {
                            "unify-native-nonempty-maude-empty"
                        },
                        format!("native {} vs Maude {}", n.len(), m.len()),
                    );
                }
                let ni: Vec<_> = n.iter().map(|a| images(a, &qvars)).collect();
                let mi: Vec<_> = m.iter().map(|a| images(a, &qvars)).collect();
                match ctx.uncovered(si, &mi, &ni) {
                    Ok(u) if !u.is_empty() => out.find(
                        "unify-INCOMPLETE",
                        format!("Maude unifier(s) {u:?} are not instances of any native unifier"),
                    ),
                    Err(e) => out.find(maude_err_class(&e), e),
                    _ => {}
                }
                match ctx.uncovered(si, &ni, &mi) {
                    Ok(u) if !u.is_empty() => {
                        if u.iter().any(|i| n_sound[*i]) {
                            out.find(
                                "unify-native-extra-sound(maude-incomplete?)",
                                format!("sound native unifier(s) {u:?} are not instances of any Maude unifier"),
                            );
                        }
                    }
                    Err(e) => out.find(maude_err_class(&e), e),
                    _ => {}
                }
            }
            Q::Match(eqs, _) | Q::MatchSk(eqs, _) => {
                let mut pvars = BTreeSet::new();
                eqs.iter().for_each(|e| vars_of(&e.rhs, &mut pvars));
                let skolem: Option<BTreeSet<(&'static str, u64)>> = match q {
                    Q::MatchSk(_, b) => {
                        pvars.retain(|x| b.contains(x));
                        Some(b.iter().map(|x| (x.name, x.idx)).collect())
                    }
                    _ => None,
                };
                let sub = if let Q::Match(_, s) = q { *s } else { 0 };
                let mut has = None;
                let mut first = None;
                if sub == 1 {
                    match ctx.native(si, &qs, |h| h.has_match_eqs(eqs)).0 {
                        Ok(b) => has = Some(b),
                        Err(e) => {
                            out.native_err("has_match", &e);
                            if !full {
                                return out;
                            }
                        }
                    }
                } else if sub == 2 {
                    match ctx.native(si, &qs, |h| h.first_match_eqs(eqs)).0 {
                        Ok(b) => first = Some(b),
                        Err(e) => {
                            out.native_err("first_match", &e);
                            if !full {
                                return out;
                            }
                        }
                    }
                }
                // `match_eqs_skolemize_both` takes `Equal { lhs = pattern, rhs = subject }`,
                // the opposite of `match_eqs`. Queries keep the `match_eqs` order.
                let flipped: Eqs = eqs
                    .iter()
                    .map(|e| Equal::new(e.rhs.clone(), e.lhs.clone()))
                    .collect();
                let call = |h: &MaudeHandle| match &skolem {
                    Some(b) => h.match_eqs_skolemize_both(&flipped, b),
                    None => h.match_eqs(eqs),
                };
                let (rn, tn) = ctx.native(si, &qs, call);
                out.native_us = tn;
                if let Err(e) = &rn {
                    out.native_err(
                        if skolem.is_some() {
                            "match_skolemize"
                        } else {
                            "match"
                        },
                        e,
                    );
                    if !full {
                        return out;
                    }
                }
                // Checked against the query alone, before the other backend is consulted.
                let sound = |a: &Sub| {
                    let mp: BTreeMap<LVar, LNTerm> = a
                        .iter()
                        .filter(|(x, _)| pvars.contains(x))
                        .cloned()
                        .collect();
                    eqs.iter().all(|e| app(&e.rhs, &mp) == canon(&e.lhs))
                };
                let mut n_sound = Vec::new();
                if let Ok(n) = &rn {
                    out.native = show_subs(n);
                    out.n_native = n.len();
                    for a in n {
                        check_subst(&mut out, "match", a, &pvars, false);
                        let ok = sound(a);
                        n_sound.push(ok);
                        if !ok {
                            out.find("match-UNSOUND", show_sub(a));
                        }
                    }
                }
                let (rm, tm) = ctx.maude(si, &qs, call);
                out.maude_us = tm;
                let m = match rm {
                    Ok(m) => m,
                    Err(e) => {
                        out.maude = format!("ERROR {e}");
                        out.find(maude_err_class(&e), e);
                        return out;
                    }
                };
                out.maude = show_subs(&m);
                out.n_maude = m.len();
                let mset: BTreeSet<Vec<LNTerm>> = m.iter().map(|a| images(a, &pvars)).collect();
                if let Some(b) = has {
                    if b == m.is_empty() {
                        out.find(
                            "has-match-MISMATCH",
                            format!("native has_match={b}, Maude has {} matcher(s)", m.len()),
                        );
                    }
                }
                if let Some(f) = &first {
                    let ok = match f {
                        None => m.is_empty(),
                        Some(a) => mset.contains(&images(a, &pvars)),
                    };
                    if !ok {
                        out.find(
                            "first-match-MISMATCH",
                            format!("native first_match={:?}", f.as_ref().map(show_sub)),
                        );
                    }
                }
                let Ok(n) = rn else { return out };
                out.listing = Some(listing(&n, &m));
                let nset: BTreeSet<Vec<LNTerm>> = n.iter().map(|a| images(a, &pvars)).collect();
                for (a, ok) in n.iter().zip(&n_sound) {
                    if *ok && !mset.contains(&images(a, &pvars)) {
                        out.find("match-native-extra-sound(maude-incomplete?)", show_sub(a));
                    }
                }
                if nset.len() != n.len() {
                    out.find(
                        "match-duplicate-answers",
                        format!("{} answers, {} distinct", n.len(), nset.len()),
                    );
                }
                for a in &m {
                    if !sound(a) {
                        out.find("oracle-maude-unsound-matcher", show_sub(a));
                    } else if !nset.contains(&images(a, &pvars)) {
                        out.find(
                            if n.is_empty() {
                                "match-INCOMPLETE-EMPTY"
                            } else {
                                "match-INCOMPLETE"
                            },
                            format!("missing matcher {}", show_sub(a)),
                        );
                    }
                }
            }
            Q::Reduce(t) => {
                let (rn, tn) = ctx.native(si, &qs, |h| h.reduce(t));
                out.native_us = tn;
                if let Err(e) = &rn {
                    out.native_err("reduce", e);
                    if !full {
                        return out;
                    }
                }
                let (rm, tm) = ctx.maude(si, &qs, |h| h.reduce(t));
                out.maude_us = tm;
                let m = match rm {
                    Ok(m) => m,
                    Err(e) => {
                        out.maude = format!("ERROR {e}");
                        out.find(maude_err_class(&e), e);
                        return out;
                    }
                };
                out.maude = show(&m);
                out.n_maude = usize::from(canon(&m) != canon(t));
                let Ok(n) = rn else { return out };
                out.native = show(&n);
                out.n_native = out.n_maude;
                if canon(&n) != canon(&m) {
                    out.find(
                        "reduce-MISMATCH",
                        format!("native {} vs Maude {}", show(&n), show(&m)),
                    );
                }
            }
            Q::Variants(ts) => {
                let t = if ts.len() == 1 {
                    ts[0].clone()
                } else {
                    f_app_list(ts.clone())
                };
                let mut qvars = BTreeSet::new();
                vars_of(&t, &mut qvars);
                let (rn, tn) = ctx.native(si, &qs, |h| h.variants(&t));
                out.native_us = tn;
                if let Err(e) = &rn {
                    out.native_err("variants", e);
                    if !full {
                        return out;
                    }
                }
                let (rm, tm) = ctx.maude(si, &qs, |h| h.variants(&t));
                out.maude_us = tm;
                let m = match rm {
                    Ok(m) => m,
                    Err(e) => {
                        out.maude = format!("ERROR {e}");
                        out.find(maude_err_class(&e), e);
                        return out;
                    }
                };
                out.maude = show_subs(&m);
                out.n_maude = m.len();
                let Ok(n) = rn else { return out };
                out.native = show_subs(&n);
                out.n_native = n.len();
                out.listing = Some(listing(&n, &m));
                if n.is_empty() {
                    out.find(
                        "variants-INCOMPLETE-EMPTY",
                        "native returned no variant at all",
                    );
                }
                let tuple =
                    |ctx: &mut Ctx, out: &mut Out, a: &Sub, native: bool| -> Option<Vec<LNTerm>> {
                        let mp: BTreeMap<LVar, LNTerm> = a.iter().cloned().collect();
                        let inst = app(&t, &mp);
                        let val = match ctx.maude(si, "<variant value>", |h| h.reduce(&inst)).0 {
                            Ok(x) => canon(&x),
                            Err(e) => {
                                out.find(maude_err_class(&e), e);
                                return None;
                            }
                        };
                        if native {
                            for (_, img) in a {
                                match ctx.maude(si, "<variant image>", |h| h.reduce(img)).0 {
                                    Ok(x) if canon(&x) != canon(img) => {
                                        out.find("variants-substitution-not-normal", show_sub(a))
                                    }
                                    _ => {}
                                }
                            }
                        }
                        let mut tup = images(a, &qvars);
                        tup.push(val);
                        Some(tup)
                    };
                let mut ni = Vec::new();
                for a in &n {
                    check_subst(&mut out, "variants", a, &qvars, true);
                    match tuple(ctx, &mut out, &freshen(a), true) {
                        Some(x) => ni.push(x),
                        None => return out,
                    }
                }
                let mut mi = Vec::new();
                for a in &m {
                    match tuple(ctx, &mut out, &freshen(a), false) {
                        Some(x) => mi.push(x),
                        None => return out,
                    }
                }
                match ctx.uncovered(si, &mi, &ni) {
                    Ok(u) if !u.is_empty() => out.find(
                        "variants-INCOMPLETE",
                        format!("Maude variant(s) {u:?} are not instances of any native variant"),
                    ),
                    Err(e) => out.find(maude_err_class(&e), e),
                    _ => {}
                }
                match ctx.uncovered(si, &ni, &mi) {
                    Ok(u) if !u.is_empty() => out.find(
                        "variants-native-extra(not-instance-of-maude-variant)",
                        format!("native variant(s) {u:?} are not instances of any Maude variant"),
                    ),
                    Err(e) => out.find(maude_err_class(&e), e),
                    _ => {}
                }
                if n.len() != m.len() {
                    out.find(
                        if n.len() > m.len() {
                            "variants-count-native-more"
                        } else {
                            "variants-count-native-fewer"
                        },
                        format!("native {} vs Maude {}", n.len(), m.len()),
                    );
                }
            }
        }
        out
    }

    fn maude_err_class(e: &str) -> String {
        if e.starts_with("TIMEOUT") {
            "oracle-maude-timeout".into()
        } else {
            let t: String = e.chars().take(60).collect();
            format!("oracle-maude-error: {}", t.replace('\n', " "))
        }
    }

    /// Classes that only count (never shrunk or logged in full after the first).
    fn informational(class: &str) -> bool {
        class.starts_with("oracle-maude-timeout")
    }

    fn shrink(ctx: &mut Ctx, si: usize, q: &Q, class: &str) -> (Q, usize) {
        let mut cur = q.clone();
        let t0 = Instant::now();
        let mut evals = 0;
        let budget = if class.contains("timeout") { 12 } else { 400 };
        'outer: loop {
            for c in query_cands(&cur) {
                if evals >= budget || t0.elapsed() > Duration::from_secs(90) {
                    break 'outer;
                }
                evals += 1;
                ctx.fresh_subject(si);
                let o = eval(ctx, si, &c, false);
                if o.findings.iter().any(|(k, _)| k == class) {
                    cur = c;
                    continue 'outer;
                }
            }
            break;
        }
        (cur, evals)
    }

    struct Seen {
        map: BTreeMap<String, (u64, (usize, usize, usize))>,
    }

    fn report(
        ctx: &mut Ctx,
        si: usize,
        q: &Q,
        out: &Out,
        seen: &mut Seen,
        origin: &str,
        do_shrink: bool,
    ) {
        let sig = ctx.sigs[si].name;
        for (class, detail) in &out.findings {
            st(&format!("F|{}|{}|{}", class, q.op(), sig));
            let key = format!("{class}|{}|{sig}", q.op());
            let e = seen.map.entry(key).or_insert((0, (usize::MAX, 0, 0)));
            e.0 += 1;
            let count = e.0;
            let best = e.1;
            if informational(class) && count > 1 {
                continue;
            }
            if count > 3 && q.measure() >= best {
                continue;
            }
            // Does a fresh session reproduce it? (State/cache dependence is a finding itself.)
            ctx.fresh_subject(si);
            let again = eval(ctx, si, q, true);
            let reproducible = again.findings.iter().any(|(k, _)| k == class);
            let (minq, evals) = if do_shrink && reproducible && !informational(class) {
                shrink(ctx, si, q, class)
            } else {
                (q.clone(), 0)
            };
            ctx.fresh_subject(si);
            let fin = eval(ctx, si, &minq, true);
            let e = seen
                .map
                .get_mut(&format!("{class}|{}|{sig}", q.op()))
                .unwrap();
            if minq.measure() < e.1 {
                e.1 = minq.measure();
            } else if count > 3 {
                continue;
            }
            let mut s = String::new();
            let _ = writeln!(
                s,
                "=== FINDING class={class:?} cfg={} sig={sig} op={} {origin} occurrence={count} fresh-session-reproducible={reproducible}",
                ctx.cfg.name(),
                q.op()
            );
            let _ = writeln!(s, "detail: {detail}");
            let _ = writeln!(s, "original:  {}", q.show());
            let _ = writeln!(
                s,
                "minimized: {}   (size {:?}, {evals} shrink evals)",
                minq.show(),
                minq.measure()
            );
            let _ = writeln!(
                s,
                "replay: {}audit_fuzz one --cfg {} --sig {sig} --op {} '{}'",
                ctx.cfg
                    .env()
                    .iter()
                    .map(|(k, v)| format!("{k}={v} "))
                    .collect::<String>(),
                ctx.cfg.name(),
                q.op(),
                minq.show()
            );
            let _ = writeln!(s, "minimized findings: {:?}", fin.findings);
            let _ = writeln!(s, "native ({}us): {}", fin.native_us, fin.native);
            let _ = writeln!(s, "maude  ({}us): {}", fin.maude_us, fin.maude);
            s.push('\n');
            append("findings", &s);
        }
    }

    fn record(sig: &str, q: &Q, out: &Out) {
        let op = q.opclass();
        st(&format!("n|{op}|{sig}"));
        st(&format!("nsub|{}|{sig}", q.op()));
        if out.findings.is_empty() {
            st(&format!("clean|{op}|{sig}"));
        }
        if out.native.starts_with("ERROR") {
            st(&format!("nerr|{op}|{sig}"));
        }
        // A native timeout counts differently when Maude answered the same query quickly.
        if out.native.starts_with("ERROR TIMEOUT") {
            let maude = if out.maude.starts_with("ERROR") {
                "maude-failed-too"
            } else if out.maude_us < 1_000_000 {
                "maude-under-1s"
            } else {
                "maude-over-1s"
            };
            st(&format!("native-timeout|{}|{sig}|{maude}", q.op()));
            append(
                "timeouts",
                &format!(
                    "sig={sig} op={} maude={maude} ({}us, {} answers): {}\n",
                    q.op(),
                    out.maude_us,
                    out.n_maude,
                    q.show()
                ),
            );
        }
        if out.n_maude > 0 {
            st(&format!("nonempty|{op}|{sig}"));
        }
        if out.n_maude > 1 {
            st(&format!("multi|{op}|{sig}"));
        }
        if let Some(l) = out.listing {
            st(&format!("listing|{op}|{sig}|{l}"));
            if l != "same" {
                let n = STATS
                    .lock()
                    .unwrap()
                    .get(&format!("listing|{op}|{sig}|{l}"))
                    .copied()
                    .unwrap_or(0);
                if n <= 5 {
                    append(
                        "listing",
                        &format!(
                            "{l} sig={sig} op={}: {}\n  native {}\n  maude  {}\n",
                            q.op(),
                            q.show(),
                            out.native.replace('\n', "\n  "),
                            out.maude.replace('\n', "\n  ")
                        ),
                    );
                }
            }
        }
        match out.n_native.cmp(&out.n_maude) {
            std::cmp::Ordering::Greater => st(&format!("count-native-more|{op}|{sig}")),
            std::cmp::Ordering::Less => st(&format!("count-native-fewer|{op}|{sig}")),
            _ => {}
        }
        let bucket = |us: u64| 64 - (us.max(1)).leading_zeros() as u64;
        st(&format!("latN|{op}|{sig}|{:02}", bucket(out.native_us)));
        st(&format!("latM|{op}|{sig}|{:02}", bucket(out.maude_us)));
        st_add(&format!("sumN_us|{op}|{sig}"), out.native_us);
        st_add(&format!("sumM_us|{op}|{sig}"), out.maude_us);
        let mut g = MAXLAT.lock().unwrap();
        for (k, us) in [("N", out.native_us), ("M", out.maude_us)] {
            let e = g
                .entry(format!("{k}|{op}|{sig}"))
                .or_insert((0, String::new()));
            if us > e.0 {
                *e = (us, format!("{} [{}]", q.show(), q.op()));
            }
        }
        drop(g);
        if out.native_us > 100_000
            || (out.native_us > 20_000 && out.native_us > 50 * out.maude_us.max(1))
        {
            st(&format!("slow-native|{op}|{sig}"));
            let n = STATS
                .lock()
                .unwrap()
                .get(&format!("slow-native|{op}|{sig}"))
                .copied()
                .unwrap_or(0);
            if n <= 25 {
                append(
                    "slow",
                    &format!(
                        "native {}us maude {}us sig={sig} op={} answers n={} m={} size={:?}: {}\n",
                        out.native_us,
                        out.maude_us,
                        q.op(),
                        out.n_native,
                        out.n_maude,
                        q.measure(),
                        q.show()
                    ),
                );
            }
        }
    }

    // ---------------------------------------------------------------- directed cases

    const DIRECTED: &[(&str, &str, &str)] = &[
        // free: occurs check, sorts
        ("free", "unify", "x = f(y,y) ; y = g(x)"),
        ("free", "unify", "x = f(y,y) ; y = g(z) ; z = h(x)"),
        ("free", "unify", "~a = h(x)"),
        ("free", "unify", "~a = $p"),
        ("free", "unify", "x = ~a"),
        ("free", "unify", "~a = ~b"),
        ("free", "unify", "$p = $q"),
        ("free", "unify", "$p = 'a'"),
        ("free", "unify", "~a = 'a'"),
        ("free", "unify", "~a = ~'n'"),
        ("free", "unify", "$p = ~'n'"),
        ("free", "unify", "pair(x,y) = pair(y,x)"),
        ("free", "unify", "f(x,g(y)) = f(g(y),x)"),
        ("free", "unify", "x = x"),
        ("free", "unify", "f(x,y) = f(x,z)"),
        ("free", "unify", "x.1 = x"),
        ("free", "unify", "f(x,~a) = f($p,y)"),
        ("free", "unify", "f(x,x) = f(~a,$p)"),
        ("free", "unify", "f(x,x) = f(~a,y) ; y = $p"),
        ("free", "unify", "pair(x,pair(y,x)) = w"),
        ("free", "unify", "h(x) = x"),
        ("free", "unify", "f(x,h(y)) = f(h(y),h(x))"),
        ("free", "unify", "k0 = k1"),
        ("free", "unify", "k0 = 'k0'"),
        ("free", "unify", "fst(x) = fst(pair(y,z))"),
        ("free", "match", "f('a','a') = f(x,x)"),
        ("free", "match", "f('a','b') = f(x,x)"),
        ("free", "match", "f(x,'a') = f(y,x)"),
        ("free", "match", "f(x,y) = f(y,x)"),
        ("free", "match", "f(x,x) = f(y,x)"),
        ("free", "match", "h(x) = x"),
        ("free", "match", "x = h(x)"),
        ("free", "match", "x = ~a"),
        ("free", "match", "~a = x"),
        ("free", "match", "~c = ~a"),
        ("free", "match", "~'n' = ~a"),
        ("free", "match", "'a' = $p"),
        ("free", "match", "'a' = ~a"),
        ("free", "match", "f(~c,$t) = f(x,x)"),
        ("free", "match", "f(~c,~c) = f(~a,x)"),
        ("free", "match", "f(r,h(r)) = f(x,h(x)) ; g(r) = g(y)"),
        ("free", "matchsk", "f(x,'a') = f(y,x) @ y"),
        ("free", "matchsk", "f(x,'a') = f(y,x) @ x y"),
        ("free", "matchsk", "f(x,x) = f(y,x) @ y"),
        ("free", "matchsk", "f('a',x) = f(y,x) @ y"),
        ("free", "matchsk", "f('a','b') = f(y,x) @ y"),
        ("free", "reduce", "fst(pair(x,y))"),
        ("free", "reduce", "snd(fst(pair(pair(x,y),z)))"),
        ("free", "reduce", "fst(x)"),
        ("free", "variants", "fst(x)"),
        ("free", "variants", "fst(x) ; snd(x)"),
        ("free", "variants", "fst(fst(x))"),
        ("free", "variants", "pair(fst(x),snd(x))"),
        ("free", "variants", "fst(x) ; fst(y)"),
        ("free", "variants", "f(fst(x),snd(y))"),
        ("free", "variants", "fst(snd(x)) ; x"),
        ("free", "variants", "fst(~a)"),
        ("free", "variants", "fst($p)"),
        ("free", "variants", "x"),
        ("free", "variants", "h('a')"),
        // multiset AC
        ("mset", "unify", "union(x,y) = union(z,w)"),
        ("mset", "unify", "union(x,x) = union(y,z)"),
        ("mset", "unify", "union(x,'a') = union(y,'b')"),
        ("mset", "unify", "union(x,x,y) = union(z,z,'a')"),
        ("mset", "unify", "x = union(x,y)"),
        ("mset", "unify", "union(x,y) = union(x,z)"),
        ("mset", "unify", "x = f(y,y) ; y = g(x)"),
        ("mset", "unify", "x = union(y,'a') ; y = union(x,'b')"),
        (
            "mset",
            "unify",
            "pair(union(x,y),x) = pair(union('a','b'),y)",
        ),
        ("mset", "unify", "union(x,h(union(x,y))) = union(z,h(z))"),
        ("mset", "unify", "union(h(x),h(y)) = union(h('a'),h(z))"),
        ("mset", "unify", "union(x,y,z) = union('a','b','c')"),
        ("mset", "unify", "union(~a,x) = union($p,y)"),
        ("mset", "unify", "union(~a,~b) = union(x,y)"),
        ("mset", "unify", "union(~a,~b) = union(~a,x)"),
        ("mset", "unify", "union(x,x) = union(~a,$p)"),
        ("mset", "unify", "union(x,x) = union(y,y,y)"),
        ("mset", "unify", "union(x,x,x) = union(y,y)"),
        ("mset", "unify", "union(x,y) = union('a','a')"),
        ("mset", "unify", "union(x,h(x)) = union(y,h('a'))"),
        ("mset", "unify", "union(x,h(y)) = union(y,h(x))"),
        (
            "mset",
            "unify",
            "f(union(x,y),union(y,z)) = f(union('a',w),union('b',w))",
        ),
        (
            "mset",
            "unify",
            "union(x,y) = union(z,'a') ; union(z,w) = union(x,'b')",
        ),
        (
            "mset",
            "unify",
            "h(union(x,h(union(y,'a')))) = h(union(h(union('a',z)),w))",
        ),
        ("mset", "unify", "union(x,y) = h(z)"),
        ("mset", "unify", "union(x,y) = ~a"),
        ("mset", "unify", "union(x,x) = union(x,y)"),
        ("mset", "match", "union('a','b','c') = union(x,y)"),
        ("mset", "match", "union('a','a','b') = union(x,x,y)"),
        ("mset", "match", "union(r,s,'a') = union(x,y)"),
        ("mset", "match", "union(x,'a') = union(x,y)"),
        ("mset", "match", "union(x,y) = union(y,x)"),
        ("mset", "match", "union(h('a'),h('b')) = union(h(x),y)"),
        ("mset", "match", "union('a',~'n') = union(~a,x)"),
        ("mset", "match", "union('a','b') = union(~a,x)"),
        ("mset", "match", "f(union('a','b'),'a') = f(union(x,y),x)"),
        ("mset", "match", "union('a','b') = x"),
        ("mset", "match", "union(r,r) = union(x,x)"),
        ("mset", "match", "union(r,s) = union(x,x)"),
        ("mset", "matchsk", "union(y,'1',h(y)) = union(y,z) @ z"),
        ("mset", "matchsk", "union(y,'1',h(y)) = union(y,z) @ y z"),
        ("mset", "matchsk", "union(x,'a') = union(x,y) @ y"),
        // DH
        ("dh", "unify", "exp(x,y) = exp(z,w)"),
        ("dh", "unify", "mult(x,y) = mult(z,inv(w))"),
        ("dh", "unify", "mult(x,inv(x)) = one"),
        ("dh", "unify", "mult(x,y,z) = mult(w,x.1)"),
        ("dh", "unify", "exp(x,x) = exp(y,z)"),
        ("dh", "unify", "exp(x,mult(x,y)) = exp(z,mult(z,w))"),
        ("dh", "unify", "mult(~a,x) = mult(~b,y)"),
        ("dh", "unify", "exp('g',mult(~a,~b)) = exp(x,y)"),
        ("dh", "unify", "exp('g',mult(~a,~b)) = exp(x,mult(y,z))"),
        ("dh", "unify", "exp(x,~a) = exp('g',mult(~a,~b))"),
        ("dh", "unify", "mult(x,y) = mult(x,z)"),
        ("dh", "unify", "x = mult(x,y)"),
        ("dh", "unify", "mult(x,inv(y)) = mult(z,inv(w))"),
        ("dh", "unify", "inv(x) = inv(mult(y,z))"),
        ("dh", "unify", "pair(exp(x,y),h(exp(y,x))) = pair(z,h(z))"),
        ("dh", "reduce", "exp(exp('g',x),y)"),
        ("dh", "reduce", "mult(x,inv(x))"),
        ("dh", "reduce", "inv(inv(x))"),
        ("dh", "reduce", "inv(mult(x,y))"),
        ("dh", "reduce", "exp(x,one)"),
        ("dh", "reduce", "exp(exp(x,y),inv(y))"),
        ("dh", "reduce", "mult(x,one)"),
        ("dh", "reduce", "exp(DH_neutral,x)"),
        ("dh", "reduce", "mult(inv(mult(x,y)),x)"),
        ("dh", "reduce", "fst(pair(exp(exp('g',~a),~b),x))"),
        ("dh", "reduce", "inv(mult(inv(x),y))"),
        ("dh", "reduce", "exp(exp('g',mult(x,y)),inv(x))"),
        ("dh", "reduce", "mult(x,mult(y,inv(x)))"),
        ("dh", "reduce", "inv(one)"),
        ("dh", "reduce", "mult(inv(x),inv(y))"),
        ("dh", "reduce", "exp(one,x)"),
        ("dh", "reduce", "exp(x,x)"),
        ("dh", "reduce", "exp(exp(x,x),inv(x))"),
        ("dh", "reduce", "mult(x,x,inv(x))"),
        ("dh", "reduce", "mult(inv(x),inv(inv(x)))"),
        ("dh", "reduce", "exp(exp(exp('g',x),y),inv(mult(x,y)))"),
        ("dh", "reduce", "h(exp(exp('g',inv(x)),x))"),
        ("dh", "reduce", "inv(mult(x,inv(mult(y,inv(x)))))"),
        ("dh", "reduce", "mult(one,one)"),
        ("dh", "reduce", "exp(exp(x,~a),inv(~a))"),
        ("dh", "reduce", "exp(DH_neutral,inv(x))"),
        ("dh", "reduce", "inv(DH_neutral)"),
        ("dh", "reduce", "mult(DH_neutral,x)"),
        ("dh", "variants", "exp(x,y)"),
        ("dh", "variants", "exp(exp('g',x),y)"),
        ("dh", "variants", "mult(x,inv(x))"),
        ("dh", "variants", "inv(inv(x))"),
        ("dh", "variants", "inv(x)"),
        ("dh", "variants", "inv(mult(x,y))"),
        ("dh", "variants", "exp('g',~a)"),
        ("dh", "variants", "exp(x,~a)"),
        ("dh", "variants", "exp(exp('g',~a),~b)"),
        ("dh", "variants", "exp(x,x)"),
        ("dh", "variants", "pair(exp(x,y),h(exp(x,y)))"),
        ("dh", "variants", "fst(pair(exp(x,y),z))"),
        ("dh", "variants", "exp(x,y) ; exp(y,x)"),
        ("dh", "variants", "exp(x,inv(y))"),
        ("dh", "variants", "exp(x,mult(~a,~b))"),
        ("dh", "variants", "mult(x,~a)"),
        ("dh", "variants", "mult(x,y)"),
        ("dh", "variants", "exp(exp(x,y),z)"),
        ("dh", "variants", "exp(fst(x),~a)"),
        ("dh", "variants", "h(exp($p,x))"),
        ("dh", "variants", "exp(x,one)"),
        // XOR
        ("xor", "unify", "xor(x,y) = xor(z,w)"),
        ("xor", "unify", "xor(x,y) = zero"),
        ("xor", "unify", "xor(x,x) = y"),
        ("xor", "unify", "xor(x,'a') = xor(y,'b')"),
        ("xor", "unify", "h(xor(x,y)) = h(xor(y,z))"),
        ("xor", "unify", "xor(x,y) = xor(x,z)"),
        ("xor", "reduce", "xor(x,x)"),
        ("xor", "reduce", "xor(x,zero)"),
        ("xor", "reduce", "xor(x,y,x)"),
        ("xor", "reduce", "h(xor(x,xor(y,x)))"),
        ("xor", "reduce", "xor(h(x),h(x),y)"),
        ("xor", "reduce", "xor(x,x,x)"),
        ("xor", "reduce", "xor(zero,zero)"),
        ("xor", "reduce", "xor(xor(x,y),xor(y,z),xor(z,x))"),
        ("xor", "reduce", "xor(h(xor(x,x)),h(zero))"),
        ("xor", "reduce", "fst(pair(xor(x,x),y))"),
        ("xor", "reduce", "xor(fst(pair(x,y)),x)"),
        ("xor", "variants", "xor(x,y)"),
        ("xor", "variants", "xor(x,x)"),
        ("xor", "variants", "xor(x,'a')"),
        ("xor", "variants", "h(xor(x,y))"),
        ("xor", "variants", "xor(x,y) ; xor(y,z)"),
        ("xor", "variants", "xor(x,h(x))"),
        ("xor", "variants", "xor(~a,x)"),
        ("xor", "variants", "xor(~a,~b)"),
        ("xor", "variants", "xor(x,y,z)"),
        ("xor", "variants", "xor(x,fst(y))"),
        ("xor", "variants", "x ; xor(x,'a')"),
        // bilinear pairing
        ("bp", "unify", "em(x,y) = em(z,w)"),
        ("bp", "unify", "em(x,y) = em(y,x)"),
        ("bp", "unify", "em(x,'a') = em('b',y)"),
        ("bp", "unify", "em(pmult(x,'P'),'Q') = em('Q',z)"),
        ("bp", "unify", "em(x,x) = em(y,z)"),
        ("bp", "unify", "em(x,h(x)) = em(h(y),y)"),
        ("bp", "unify", "em(~a,x) = em(y,$p)"),
        ("bp", "unify", "pair(em(x,y),x) = pair(em('a','b'),z)"),
        ("bp", "unify", "em(em(x,y),z) = em(w,em('a','b'))"),
        ("bp", "match", "em('a','b') = em(x,y)"),
        ("bp", "match", "em('a','a') = em(x,y)"),
        ("bp", "match", "em('a','b') = em(x,x)"),
        ("bp", "match", "em(r,s) = em(x,y)"),
        ("bp", "match", "em(h('a'),'a') = em(x,h(x))"),
        ("bp", "reduce", "em(pmult(x,'P'),'Q')"),
        ("bp", "reduce", "pmult(x,pmult(y,'P'))"),
        ("bp", "reduce", "em(pmult(x,'P'),pmult(y,'Q'))"),
        ("bp", "reduce", "exp(em('P','Q'),x)"),
        ("bp", "reduce", "pmult(one,'P')"),
        ("bp", "reduce", "pmult(inv(x),pmult(x,'P'))"),
        ("bp", "reduce", "em(pmult(x,'P'),pmult(inv(x),'Q'))"),
        ("bp", "reduce", "exp(em(pmult(x,'P'),'Q'),inv(x))"),
        ("bp", "reduce", "pmult(x,pmult(y,pmult(z,'P')))"),
        ("bp", "reduce", "em('P',pmult(x,'Q'))"),
        ("bp", "variants", "em(pmult(x,'P'),'Q')"),
        ("bp", "variants", "pmult(x,pmult(y,'P'))"),
        ("bp", "variants", "pmult(x,y)"),
        ("bp", "variants", "em(x,y)"),
        ("bp", "variants", "em(x,'Q')"),
        ("bp", "variants", "pmult(~a,'P')"),
        ("bp", "variants", "em(pmult(~a,'P'),pmult(~b,'Q'))"),
        // natural numbers
        ("nat", "unify", "tplus(%n,%m) = tplus(%k,tone)"),
        ("nat", "unify", "tplus(%n,tone) = %n"),
        ("nat", "unify", "%n = x"),
        ("nat", "unify", "%n = tone"),
        ("nat", "unify", "%n = 'a'"),
        ("nat", "unify", "tplus(%n,%n) = tplus(%m,tone,tone)"),
        ("nat", "unify", "x = tplus(tone,tone)"),
        ("nat", "unify", "%n = ~a"),
        ("nat", "unify", "%n = $p"),
        ("nat", "unify", "pair(%n,x) = pair(y,%m)"),
        ("nat", "unify", "x = tplus(%n,tone) ; x = tplus(%m,%m)"),
        ("nat", "unify", "h(%n) = h(tplus(%m,tone))"),
        ("nat", "unify", "tplus(%n,%m) = tplus(%n,%k)"),
        ("nat", "unify", "x = y ; x = %n ; y = h(z)"),
        ("nat", "match", "tplus(tone,tone,tone) = tplus(%n,%m)"),
        ("nat", "match", "tplus(tone,tone) = %n"),
        ("nat", "match", "tone = x"),
        ("nat", "match", "'a' = %n"),
        ("nat", "match", "tplus(%j,tone) = tplus(%n,%m)"),
        ("nat", "match", "tplus(%j,tone) = x"),
        ("nat", "match", "r = %n"),
        ("nat", "variants", "tplus(%n,tone)"),
        ("nat", "variants", "fst(pair(%n,x))"),
        ("nat", "reduce", "tplus(tone,tplus(tone,%n))"),
        // user equations
        ("user", "reduce", "sdec(senc(x,y),y)"),
        ("user", "reduce", "sdec(senc(x,y),z)"),
        ("user", "reduce", "verify(sign(x,y),x,pk(y))"),
        ("user", "reduce", "verify(sign(x,y),z,pk(y))"),
        ("user", "reduce", "eqt(x,x)"),
        ("user", "reduce", "eqt(x,y)"),
        ("user", "reduce", "g0(k0)"),
        ("user", "reduce", "g0(k1)"),
        ("user", "reduce", "g0(g0(k0))"),
        ("user", "reduce", "open(seal(seal(x,y),z),z,y)"),
        ("user", "reduce", "open(seal(seal(x,y),z),y,z)"),
        ("user", "reduce", "open(seal(seal(x,y),y),y,y)"),
        ("user", "reduce", "fst(sdec(senc(pair(x,y),z),z))"),
        ("user", "reduce", "sdec(sdec(senc(senc(x,y),z),z),y)"),
        ("user", "reduce", "eqt(sdec(senc(x,y),y),x)"),
        ("user", "reduce", "adec(aenc(x,pk(y)),y)"),
        ("user", "reduce", "eqt(fst(pair(x,y)),snd(pair(y,x)))"),
        ("user", "variants", "sdec(x,y)"),
        ("user", "variants", "sdec(sdec(x,y),z)"),
        ("user", "variants", "fst(sdec(x,y))"),
        ("user", "variants", "verify(x,y,z)"),
        ("user", "variants", "verify(x,y,pk(z))"),
        ("user", "variants", "eqt(x,y)"),
        ("user", "variants", "eqt(fst(x),snd(x))"),
        ("user", "variants", "eqt(x,h(y))"),
        ("user", "variants", "eqt(x,h(x))"),
        ("user", "variants", "eqt(~a,$p)"),
        ("user", "variants", "eqt(~a,~b)"),
        ("user", "variants", "eqt(~a,x)"),
        ("user", "variants", "g0(x)"),
        ("user", "variants", "g0(~a)"),
        ("user", "variants", "open(x,y,z)"),
        ("user", "variants", "open(seal(x,y),z,w)"),
        ("user", "variants", "open(x,y,y)"),
        ("user", "variants", "fst(x) ; snd(x)"),
        ("user", "variants", "sdec(x,y) ; sdec(x,z)"),
        ("user", "variants", "pair(fst(x),snd(x))"),
        ("user", "variants", "adec(x,y)"),
        ("user", "variants", "fst(fst(x))"),
        ("user", "variants", "sdec(fst(x),snd(x))"),
        ("user", "variants", "sdec(x,~a)"),
        ("user", "variants", "sdec(~a,x)"),
        ("user", "variants", "sdec(x,x)"),
        ("user", "variants", "eqt(sdec(x,y),z)"),
        ("user", "variants", "g0(fst(x))"),
        ("user", "unify", "sdec(x,y) = sdec(senc(z,w),w)"),
        ("user", "unify", "eqt(x,x) = true"),
        // user AC symbol
        ("userac", "unify", "merge(x,y) = merge(z,w)"),
        ("userac", "unify", "merge(x,'a') = merge(y,'b')"),
        ("userac", "unify", "merge(x,h(merge(x,y))) = merge(z,h(z))"),
        ("userac", "unify", "merge(x,x) = merge(y,z)"),
        ("userac", "unify", "x = merge(x,y)"),
        ("userac", "match", "merge('a','b','c') = merge(x,y)"),
        ("userac", "reduce", "fst(pair(merge(x,y),z))"),
        ("userac", "variants", "fst(merge(x,y))"),
        ("userac", "variants", "merge(fst(x),y)"),
        // combinations
        ("combo", "unify", "union(x,y) = union(xor(x,z),w)"),
        ("combo", "unify", "xor(x,mult(x,y)) = xor(z,mult(z,w))"),
        (
            "combo",
            "unify",
            "pair(union(x,y),xor(x,y)) = pair(union(z,w),xor(z,w))",
        ),
        (
            "combo",
            "unify",
            "h(union(x,h(xor(x,y)))) = h(union(z,h(xor(w,'a'))))",
        ),
        (
            "combo",
            "unify",
            "union(x,mult(y,z)) = union(mult(x,w),'a')",
        ),
        ("combo", "unify", "xor(x,y) = mult(z,w)"),
        ("combo", "unify", "union(x,y) = xor(z,w)"),
        ("combo", "unify", "union(mult(x,y),xor(x,y)) = union(z,w)"),
        (
            "combo",
            "unify",
            "union(x,xor(y,'a')) = union(y,xor(x,'a'))",
        ),
        (
            "combo",
            "match",
            "union(xor('a','b'),mult('a','b')) = union(xor(x,y),mult(x,y))",
        ),
        (
            "combo",
            "match",
            "union(xor('a','b'),mult('a','c')) = union(xor(x,y),mult(x,y))",
        ),
        (
            "combo",
            "reduce",
            "sdec(senc(xor(x,x),exp(exp('g',y),z)),exp(exp('g',z),y))",
        ),
        ("combo", "reduce", "xor(exp(x,one),x)"),
        ("combo", "reduce", "fst(pair(mult(x,inv(x)),y))"),
        ("combo", "reduce", "verify(sign(xor(x,zero),y),x,pk(y))"),
        (
            "combo",
            "reduce",
            "eqt(exp(exp('g',x),y),exp(exp('g',y),x))",
        ),
        ("combo", "reduce", "union(xor(x,x),exp(y,one))"),
        (
            "combo",
            "reduce",
            "open(seal(seal(x,mult(y,one)),xor(z,zero)),z,y)",
        ),
        ("combo", "reduce", "sdec(senc(x,xor(y,z)),xor(z,y))"),
        ("combo", "variants", "sdec(x,exp(y,z))"),
        ("combo", "variants", "xor(fst(x),y)"),
        ("combo", "variants", "sdec(xor(x,y),z)"),
        ("combo", "variants", "eqt(exp(x,y),z)"),
        ("combo", "variants", "union(x,y)"),
        ("combo", "variants", "union(fst(x),y)"),
        ("combo", "variants", "exp(x,y) ; xor(x,y)"),
        (
            "bpxornat",
            "unify",
            "em(xor(x,y),%n) = em(tplus(%m,tone),xor(z,'a'))",
        ),
        (
            "bpxornat",
            "reduce",
            "em(pmult(x,xor(y,y)),pmult(inv(x),zero))",
        ),
        ("bpxornat", "variants", "pmult(x,xor(y,'a'))"),
    ];

    // ---------------------------------------------------------------- drivers

    fn args() -> BTreeMap<String, String> {
        let mut m = BTreeMap::new();
        let a: Vec<String> = std::env::args().skip(2).collect();
        let mut i = 0;
        while i < a.len() {
            if let Some(k) = a[i].strip_prefix("--") {
                if i + 1 < a.len() && !a[i + 1].starts_with("--") {
                    m.insert(k.to_owned(), a[i + 1].clone());
                    i += 2;
                } else {
                    m.insert(k.to_owned(), "1".into());
                    i += 1;
                }
            } else {
                m.insert("_".into(), a[i].clone());
                i += 1;
            }
        }
        m
    }

    fn setup(a: &BTreeMap<String, String>, tag: Option<String>) {
        let num = |k: &str, d: u64| a.get(k).map_or(d, |s| s.parse().expect("number"));
        LIMITS
            .set((
                num("soft-ms", 10_000),
                num("hard-ms", 16_000),
                num("maude-ms", 20_000),
                num("rss-mb", 6000),
            ))
            .unwrap();
        if let (Some(dir), Some(tag)) = (a.get("out"), tag) {
            std::fs::create_dir_all(dir).unwrap();
            OUT.set((dir.clone(), tag)).unwrap();
        }
        std::thread::spawn(watchdog);
    }

    fn weights(a: &BTreeMap<String, String>) -> [usize; 5] {
        let mut w = [35, 25, 5, 20, 15];
        if let Some(s) = a.get("weights") {
            for (i, x) in s.split(',').enumerate() {
                w[i] = x.parse().expect("weight");
            }
        }
        w
    }

    fn worker(a: BTreeMap<String, String>) {
        let cfg = Cfg::parse(&a["cfg"]);
        let seed: u64 = a["seed"].parse().unwrap();
        let wid: u64 = a["wid"].parse().unwrap();
        let nw: u64 = a["workers"].parse().unwrap();
        let start: u64 = a.get("start").map_or(0, |s| s.parse().unwrap());
        let iters: u64 = a["iters"].parse().unwrap();
        let tag = format!("{}-s{seed}-w{wid}", cfg.name());
        setup(&a, Some(tag.clone()));
        SUFFIX.set(format!("from{start}")).unwrap();
        let mut ctx = Ctx::new(cfg, a.contains_key("theory"));
        let sel: Vec<usize> = match a.get("sigs") {
            Some(s) => s.split(',').map(|n| ctx.sig_index(n)).collect(),
            None => (0..ctx.sigs.len()).collect(),
        };
        let w = weights(&a);
        let heavy = a.contains_key("heavy");
        let trace = a.contains_key("trace");
        let shapes: usize = a
            .get("shapes")
            .map_or(0, |s| s.parse().expect("--shapes PCT"));
        let deadline: Option<u64> = a.get("deadline").map(|s| s.parse().expect("--deadline"));
        let mut seen = Seen {
            map: BTreeMap::new(),
        };
        let progress = format!("{}/progress-{tag}", a["out"]);
        let mut i = start;
        let t0 = Instant::now();
        let mut done = 0u64;
        while i < iters {
            if deadline.is_some_and(|d| unix_now() >= d) {
                break;
            }
            if i % nw == wid {
                let _ = std::fs::write(&progress, i.to_string());
                let mut rng = Rng::new(seed ^ i.wrapping_mul(0x9E37_79B9_7F4A_7C15));
                let si = *rng.pick(&sel);
                let q = gen_query(&mut rng, &ctx.sigs[si], &w, heavy, shapes);
                *META.lock().unwrap() = format!(
                    "cfg={} sig={} op={} seed={seed} iter={i}",
                    cfg.name(),
                    ctx.sigs[si].name,
                    q.op()
                );
                if trace {
                    append(
                        "trace",
                        &format!("{i}\t{}\t{}\t{}\n", ctx.sigs[si].name, q.op(), q.show()),
                    );
                }
                let out = eval(&mut ctx, si, &q, true);
                record(ctx.sigs[si].name, &q, &out);
                if !out.findings.is_empty() {
                    report(
                        &mut ctx,
                        si,
                        &q,
                        &out,
                        &mut seen,
                        &format!("seed={seed} iter={i}"),
                        true,
                    );
                }
                done += 1;
                if done % 500 == 0 {
                    flush_stats(SUFFIX.get().unwrap());
                }
            }
            i += 1;
        }
        flush_stats(SUFFIX.get().unwrap());
        let _ = std::fs::write(&progress, "done");
        eprintln!("worker {tag}: {done} iterations in {:?}", t0.elapsed());
        kill_children();
    }

    fn unix_now() -> u64 {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.as_secs())
    }

    fn drive(a: BTreeMap<String, String>) {
        let cfg = Cfg::parse(&a["cfg"]);
        let nw: u64 = a.get("workers").map_or(8, |s| s.parse().unwrap());
        let seed = a.get("seed").cloned().unwrap_or_else(|| "1".into());
        let out = a["out"].clone();
        std::fs::create_dir_all(&out).unwrap();
        let exe = std::env::current_exe().unwrap();
        let deadline: Option<u64> = a
            .get("seconds")
            .map(|s| unix_now() + s.parse::<u64>().expect("--seconds"));
        let spawn = |wid: u64, start: u64| {
            let mut c = std::process::Command::new(&exe);
            c.arg("worker");
            for (k, v) in &a {
                if k != "start" && k != "workers" && k != "seed" && k != "seconds" {
                    c.arg(format!("--{k}")).arg(v);
                }
            }
            c.args(["--seed", &seed, "--workers", &nw.to_string()]);
            c.args(["--wid", &wid.to_string(), "--start", &start.to_string()]);
            if let Some(d) = deadline {
                c.args(["--deadline", &d.to_string()]);
            }
            for k in [
                "TAM_RS_NATIVE_REFERENCE",
                "TAM_RS_NATIVE_REFERENCE_VARIANTS",
            ] {
                c.env_remove(k);
            }
            for (k, v) in cfg.env() {
                c.env(k, v);
            }
            let log = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(format!("{out}/worker-{}-s{seed}-w{wid}.stderr", cfg.name()))
                .unwrap();
            c.stderr(log).stdout(std::process::Stdio::null());
            c.spawn().expect("spawn worker")
        };
        let mut kids: Vec<_> = (0..nw).map(|w| (w, spawn(w, 0), 0u32)).collect();
        while !kids.is_empty() {
            std::thread::sleep(Duration::from_millis(500));
            let mut next = Vec::new();
            for (w, mut child, restarts) in kids {
                match child.try_wait().unwrap() {
                    None => next.push((w, child, restarts)),
                    Some(status) if status.success() => {}
                    Some(status) => {
                        let p = std::fs::read_to_string(format!(
                            "{out}/progress-{}-s{seed}-w{w}",
                            cfg.name()
                        ))
                        .unwrap_or_default();
                        eprintln!("worker {w} exited with {status} at iteration {p}");
                        if let (Ok(i), true) = (p.trim().parse::<u64>(), restarts < 500) {
                            next.push((w, spawn(w, i + 1), restarts + 1));
                        }
                    }
                }
            }
            kids = next;
        }
    }

    fn directed(a: BTreeMap<String, String>) {
        let cfg = Cfg::parse(&a["cfg"]);
        setup(&a, Some(format!("{}-directed", cfg.name())));
        SUFFIX.set("all".into()).unwrap();
        let mut ctx = Ctx::new(cfg, a.contains_key("theory"));
        let mut seen = Seen {
            map: BTreeMap::new(),
        };
        let from: usize = a.get("from").map_or(0, |s| s.parse().unwrap());
        for (k, (sig, op, text)) in DIRECTED.iter().enumerate().skip(from) {
            let si = ctx.sig_index(sig);
            let base = parse_query(op, text).unwrap_or_else(|e| panic!("{text}: {e}"));
            let mut qs = vec![base.clone()];
            match &base {
                Q::Unify(e, _) => qs.push(Q::Unify(e.clone(), 1)),
                Q::Match(e, _) => {
                    qs.push(Q::Match(e.clone(), 1));
                    qs.push(Q::Match(e.clone(), 2));
                }
                _ => {}
            }
            for q in qs {
                *META.lock().unwrap() =
                    format!("cfg={} sig={sig} op={} directed#{k}", cfg.name(), q.op());
                let out = eval(&mut ctx, si, &q, true);
                record(sig, &q, &out);
                println!(
                    "{:>3} {:8} {:10} n={:<3} m={:<3} {:>8}us {:>8}us {} {}",
                    k,
                    sig,
                    q.op(),
                    out.n_native,
                    out.n_maude,
                    out.native_us,
                    out.maude_us,
                    if out.findings.is_empty() {
                        "ok".to_owned()
                    } else {
                        format!(
                            "{:?}",
                            out.findings.iter().map(|f| &f.0).collect::<Vec<_>>()
                        )
                    },
                    text
                );
                if !out.findings.is_empty() {
                    report(
                        &mut ctx,
                        si,
                        &q,
                        &out,
                        &mut seen,
                        &format!("directed#{k}"),
                        false,
                    );
                    // Later cases must not inherit a latched failure.
                    ctx.fresh_subject(si);
                }
            }
        }
        flush_stats("all");
        kill_children();
    }

    fn one(a: BTreeMap<String, String>) {
        let cfg = Cfg::parse(&a["cfg"]);
        setup(&a, None);
        let mut ctx = Ctx::new(cfg, a.contains_key("theory"));
        ctx.maude_only = a.contains_key("maude-only");
        let si = ctx.sig_index(&a["sig"]);
        let q = parse_query(&a["op"], &a["_"]).unwrap_or_else(|e| panic!("{e}"));
        let out = eval(&mut ctx, si, &q, true);
        println!(
            "query [{} / {} / {}]: {}",
            cfg.name(),
            a["sig"],
            q.op(),
            q.show()
        );
        println!("native ({}us): {}", out.native_us, out.native);
        println!("maude  ({}us): {}", out.maude_us, out.maude);
        println!("findings: {:#?}", out.findings);
        if a.contains_key("shrink") {
            for (class, _) in &out.findings {
                let (m, evals) = shrink(&mut ctx, si, &q, class);
                println!("minimized for {class:?} ({evals} evals): {}", m.show());
            }
        }
        kill_children();
    }

    /// Replays the queries of a trace file (`ITER<TAB>SIG<TAB>OP<TAB>QUERY` per line) in one
    /// session, for findings that depend on what the session answered before.
    fn seq(a: BTreeMap<String, String>) {
        let cfg = Cfg::parse(&a["cfg"]);
        setup(&a, None);
        let mut ctx = Ctx::new(cfg, a.contains_key("theory"));
        let text = std::fs::read_to_string(&a["_"]).expect("trace file");
        for line in text.lines() {
            let f: Vec<&str> = line.split('\t').collect();
            if f.len() != 4 {
                continue;
            }
            let si = ctx.sig_index(f[1]);
            let q = parse_query(f[2], f[3]).unwrap_or_else(|e| panic!("{e}"));
            let out = eval(&mut ctx, si, &q, true);
            println!(
                "{}\t{}\t{}\t{}\tn={} m={} {:?}",
                f[0],
                f[1],
                f[2],
                f[3],
                out.n_native,
                out.n_maude,
                out.findings.iter().map(|x| &x.0).collect::<Vec<_>>()
            );
        }
        kill_children();
    }

    fn selftest() {
        let sigs = sigs();
        let mut n = 0;
        for (si, sig) in sigs.iter().enumerate() {
            for i in 0..3000u64 {
                let mut rng = Rng::new(i * 31 + si as u64);
                let shapes = if i % 3 == 0 { 100 } else { 0 };
                let q = gen_query(&mut rng, sig, &[35, 25, 5, 20, 15], i % 2 == 0, shapes);
                let text = q.show();
                let back = parse_query(q.op(), &text).unwrap_or_else(|e| panic!("{text}: {e}"));
                assert!(back == q, "round trip changed {text} -> {}", back.show());
                assert!(
                    q.terms().iter().all(|t| canon(t) == **t),
                    "non-canonical {text}"
                );
                n += 1;
            }
        }
        for (_, op, text) in DIRECTED {
            parse_query(op, text).unwrap_or_else(|e| panic!("{text}: {e}"));
        }
        println!(
            "selftest ok: {n} generated queries, {} directed",
            DIRECTED.len()
        );
    }

    pub fn main() {
        let mode = std::env::args().nth(1).unwrap_or_default();
        let a = args();
        match mode.as_str() {
            "drive" => drive(a),
            "worker" => worker(a),
            "directed" => directed(a),
            "one" => one(a),
            "seq" => seq(a),
            "selftest" => selftest(),
            _ => eprintln!(
                "usage: audit_fuzz drive|worker|directed|one|seq|selftest ... (see the file header)"
            ),
        }
    }
}
