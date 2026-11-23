//! Runaway searches inside one Lean call stop on cancellation and at the
//! work bound, with the clean error of each and without a reply.
use super::*;
use std::time::{Duration, Instant};
use tamarin_term::builtin::{emap, hash, msg_var, nat_plus, pair};
use tamarin_term::function_symbols::{Constructability, NoEqSym, Privacy};
use tamarin_term::maude_sig::{bp_maude_sig, hash_maude_sig, nat_maude_sig};
use tamarin_term::rewriting::RRule;
use tamarin_term::subterm_rule::rrule_to_ctxt_st_rule;
use tamarin_term::term::f_app_no_eq;
use tamarin_utils::cancellation::{CancellationGuard, CancellationToken};

/// A stopped call has to return within this long. Measured: under 60 ms after
/// a cancellation, and about 0.1 s and 1 s to spend the work bound below.
const PROMPT: Duration = Duration::from_secs(2);
/// The searches below run for minutes when nothing stops them.
const HEAD_START: Duration = Duration::from_millis(300);

fn nat(name: &str) -> LNTerm {
    Term::Lit(Lit::Var(LVar::new(name, LSort::Nat, 0)))
}

fn nat_sum(terms: &[&LNTerm]) -> LNTerm {
    let mut terms = terms.iter().rev().map(|term| (*term).clone());
    let last = terms.next().unwrap();
    terms.fold(last, |tail, head| nat_plus(head, tail))
}

/// `i+i+i+i+j+j+j+n = l+l+l+m+m+m+k+k` over natural numbers: 178 basis
/// solutions, and a family that reaches 7 GB within 8 s when it is listed.
fn wide_sums() -> Equal<LNTerm> {
    let [i, j, n, l, m, k] = ["i", "j", "n", "l", "m", "k"].map(nat);
    Equal {
        lhs: nat_sum(&[&i, &i, &i, &i, &j, &j, &j, &n]),
        rhs: nat_sum(&[&l, &l, &l, &m, &m, &m, &k, &k]),
    }
}

fn naturals() -> MaudeHandle {
    MaudeHandle::start_with_backend(MISSING, nat_maude_sig(), AlgebraBackend::NativeOnly).unwrap()
}

/// Run `call` under a token that is cancelled after [`HEAD_START`], and
/// return its result with the time it took to return after the request.
fn cancelled<T>(call: impl FnOnce() -> T) -> (T, Duration) {
    let token = CancellationToken::default();
    let _guard = CancellationGuard::new(Some(token.clone()));
    let canceller = std::thread::spawn(move || {
        std::thread::sleep(HEAD_START);
        token.request_cancel();
        Instant::now()
    });
    let result = call();
    let returned = Instant::now();
    let requested = canceller.join().unwrap();
    (result, returned.saturating_duration_since(requested))
}

#[test]
fn a_runaway_unification_stops_when_its_request_is_cancelled() {
    let h = naturals();
    let (result, latency) = cancelled(|| h.unify(&[wide_sums()]));
    assert!(matches!(result, Err(MaudeError::Cancelled)), "{result:?}");
    assert!(latency < PROMPT, "returned {latency:?} after the request");
    eprintln!("unify: returned {latency:?} after cancellation");
    // Cancellation is not a failure of the session, and nothing was stored:
    // the same handle answers the next request.
    h.check_backend_status().unwrap();
    let small = Equal {
        lhs: nat_plus(nat("i"), nat("j")),
        rhs: nat_plus(nat("l"), nat("m")),
    };
    assert_eq!(h.unify(&[small]).unwrap().len(), 7);
}

#[test]
fn a_runaway_unifiability_decision_stops_when_its_request_is_cancelled() {
    // A constant among the operands sends the decision to the listing.
    let h = native();
    let [u, y, x, z, w] = ["u", "y", "x", "z", "w"].map(variable);
    let side = |terms: &[&LNTerm]| {
        f_app_ac(
            AcSym::Union,
            terms.iter().map(|term| (*term).clone()).collect(),
        )
    };
    let a = pub_term("a");
    let eq = Equal {
        lhs: side(&[&a, &u, &u, &u, &u, &y, &y, &y, &y, &y]),
        rhs: side(&[&x, &x, &x, &x, &z, &z, &z, &z, &z, &w]),
    };
    let (result, latency) = cancelled(|| h.unifiable(std::slice::from_ref(&eq)));
    assert!(matches!(result, Err(MaudeError::Cancelled)), "{result:?}");
    assert!(latency < PROMPT, "returned {latency:?} after the request");
    eprintln!("unifiable: returned {latency:?} after cancellation");
    h.check_backend_status().unwrap();
}

#[test]
fn a_runaway_unification_stops_at_its_work_bound() {
    let mut h = naturals();
    h.set_search_work(1 << 20);
    let started = Instant::now();
    let error = h.unify(&[wide_sums()]).unwrap_err();
    let elapsed = started.elapsed();
    let message = error.to_string();
    assert!(
        message.contains("out of budget") && message.contains("TAM_RS_ALGEBRA_SEARCH_WORK"),
        "{message}"
    );
    assert!(elapsed < PROMPT, "stopped after {elapsed:?}");
    eprintln!("unify: stopped by the work bound after {elapsed:?}");
    // The request was not answered, so the session cannot publish a result.
    assert!(h.check_backend_status().is_err());
    // The bound is on one call: a request within it is unaffected by a
    // generous bound.
    let mut roomy = naturals();
    roomy.set_search_work(1 << 20);
    let small = Equal {
        lhs: nat_plus(nat("i"), nat("j")),
        rhs: nat_plus(nat("l"), nat("m")),
    };
    assert_eq!(roomy.unify(&[small]).unwrap().len(), 7);
    roomy.check_backend_status().unwrap();
}

fn symbol(name: &[u8], arity: usize) -> NoEqSym {
    NoEqSym::new(name, arity, Privacy::Public, Constructability::Constructor)
}

fn select(a: LNTerm, b: LNTerm) -> LNTerm {
    f_app_no_eq(symbol(b"select", 2), vec![a, b])
}

/// A theory whose one user rule matches a product of three variables before
/// the argument that decides the match:
/// `select(pair(v0+v1+v2, hash(r)), emap(a, b)) -> r`.
fn selecting() -> MaudeHandle {
    let mut sig = mset_maude_sig()
        .merge(pair_maude_sig())
        .merge(hash_maude_sig())
        .merge(bp_maude_sig());
    sig.st_fun_syms.insert(symbol(b"select", 2));
    let product = f_app_ac(AcSym::Union, (0..3).map(|i| msg_var("v", i)).collect());
    let lhs = select(
        pair(product, hash(msg_var("r", 0))),
        emap(msg_var("a", 0), msg_var("b", 0)),
    );
    sig.st_rules
        .insert(rrule_to_ctxt_st_rule(&RRule::new(lhs, msg_var("r", 0))).unwrap());
    MaudeHandle::start_for_tamarin_theory(
        MISSING,
        sig.refresh(),
        AlgebraBackend::NativeOnly,
        Arc::new(SharedMaudeCaches::default()),
    )
    .unwrap()
}

/// An irreducible instance of the rule's first argument beside a second
/// argument that is no pairing: the search for a first match tries the ways
/// of sharing `width` operands among three variables, and every one fails.
fn unselected(width: usize) -> LNTerm {
    let product = f_app_ac(
        AcSym::Union,
        (0..width).map(|i| pub_term(format!("f{i}"))).collect(),
    );
    select(pair(product, hash(variable("x"))), pub_term("other"))
}

#[test]
fn a_runaway_reduction_stops_when_its_request_is_cancelled() {
    let h = selecting();
    // The same search ends by itself on a narrow product.
    let narrow = unselected(6);
    assert_eq!(h.reduce(&narrow).unwrap(), narrow);
    let wide = unselected(64);
    let (result, latency) = cancelled(|| h.reduce(&wide));
    assert!(matches!(result, Err(MaudeError::Cancelled)), "{result:?}");
    assert!(latency < PROMPT, "returned {latency:?} after the request");
    eprintln!("reduce: returned {latency:?} after cancellation");
    h.check_backend_status().unwrap();
    assert_eq!(h.reduce(&narrow).unwrap(), narrow);
}

#[test]
fn a_runaway_reduction_stops_at_its_work_bound() {
    let mut h = selecting();
    h.set_search_work(1 << 20);
    let narrow = unselected(6);
    assert_eq!(h.reduce(&narrow).unwrap(), narrow);
    let started = Instant::now();
    let error = h.reduce(&unselected(64)).unwrap_err();
    let elapsed = started.elapsed();
    let message = error.to_string();
    assert!(
        message.contains("out of budget") && message.contains("reduction"),
        "{message}"
    );
    assert!(elapsed < PROMPT, "stopped after {elapsed:?}");
    eprintln!("reduce: stopped by the work bound after {elapsed:?}");
    assert!(h.check_backend_status().is_err());
}

/// `LIST(x*y, x*inv(y))` over Diffie-Hellman exponents. The join solver
/// proposes 247 variants, and the certificate checker does not finish them:
/// the cost is inside the unifications of its narrowing layers (stopped
/// after 900 s at 7.7 GB when nothing interrupted it).
fn joint_product_and_quotient() -> LNTerm {
    use tamarin_term::builtin::{inv, mult};
    use tamarin_term::term::f_app_list;
    let [x, y] = ["x", "y"].map(variable);
    f_app_list(vec![mult(x.clone(), y.clone()), mult(x, inv(y))])
}

fn exponents() -> MaudeHandle {
    MaudeHandle::start_with_backend(
        MISSING,
        tamarin_term::maude_sig::dh_maude_sig(),
        AlgebraBackend::NativeOnly,
    )
    .unwrap()
}

#[test]
fn a_runaway_variant_check_stops_when_its_request_is_cancelled() {
    let h = exponents();
    let query = joint_product_and_quotient();
    let (result, latency) = cancelled(|| h.variants(&query));
    assert!(matches!(result, Err(MaudeError::Cancelled)), "{result:?}");
    assert!(latency < PROMPT, "returned {latency:?} after the request");
    eprintln!("variant check: returned {latency:?} after cancellation");
    // Cancellation is not a failure of the session.
    h.check_backend_status().unwrap();
    let small = tamarin_term::builtin::mult(variable("x"), variable("y"));
    assert!(!h.variants(&small).unwrap().is_empty());
}

#[test]
fn a_runaway_variant_check_stops_at_its_search_bound() {
    let mut h = exponents();
    h.set_variant_check_search(1 << 20);
    let started = Instant::now();
    let error = h.variants(&joint_product_and_quotient()).unwrap_err();
    let elapsed = started.elapsed();
    let message = error.to_string();
    assert!(
        message.contains("out of budget")
            && message.contains("variant check")
            && message.contains("TAM_RS_VARIANT_CHECK_SEARCH"),
        "{message}"
    );
    assert!(elapsed < 4 * PROMPT, "stopped after {elapsed:?}");
    eprintln!("variant check: stopped by the search bound after {elapsed:?}");
    // The family was not certified, so the session cannot publish a result.
    assert!(h.check_backend_status().is_err());
}

/// `mult('c',w,w,y)` over Diffie-Hellman exponents has no specialised solver,
/// so the folding proposer searches for its variants, and one call of it
/// does not return within minutes: the cost is inside the unifications of a
/// product with a repeated variable. A fuzzing run found it deaf to its
/// cancellation.
#[test]
fn a_runaway_variant_search_stops_when_its_request_is_cancelled() {
    use tamarin_term::builtin::mult;
    let h = exponents();
    let [w, y] = ["w", "y"].map(variable);
    let query = f_app_ac(AcSym::Mult, vec![pub_term("c"), w.clone(), w, y]);
    let (result, latency) = cancelled(|| h.variants(&query));
    assert!(matches!(result, Err(MaudeError::Cancelled)), "{result:?}");
    assert!(latency < PROMPT, "returned {latency:?} after the request");
    eprintln!("variant search: returned {latency:?} after cancellation");
    h.check_backend_status().unwrap();
    let small = mult(variable("x"), variable("y"));
    assert!(!h.variants(&small).unwrap().is_empty());
}

/// Not a regression test: without a request to stop, the wide reduction
/// runs until the harness kills it. Run it under a timeout to see the
/// behavior the other tests exclude.
#[test]
#[ignore = "runs for minutes: the uninterrupted search, for comparison"]
fn the_wide_reduction_does_not_end_by_itself() {
    let mut h = selecting();
    h.set_search_work(0);
    let started = Instant::now();
    let result = h.reduce(&unselected(64));
    panic!("returned {result:?} after {:?}", started.elapsed());
}

fn small_sums() -> Equal<LNTerm> {
    Equal {
        lhs: nat_plus(nat("i"), nat("j")),
        rhs: nat_plus(nat("l"), nat("m")),
    }
}

/// Workers with the stack of the prover's own: a Lean search recurses.
fn workers(threads: usize) -> rayon::ThreadPool {
    rayon::ThreadPoolBuilder::new()
        .num_threads(threads)
        .stack_size(64 * 1024 * 1024)
        .build()
        .unwrap()
}

/// A parallel job runs under a scope of its request. The Lean call polls one
/// flag byte, the scope's, so a request made on the enclosing token has to
/// reach that byte at once and not only when the cleanup callbacks run.
#[test]
fn a_search_under_a_scope_stops_when_the_enclosing_request_is_cancelled() {
    use tamarin_utils::cancellation::CancellationScope;
    // Without a work bound, only the flag can stop the search.
    let mut h = naturals();
    h.set_search_work(0);
    let request = CancellationToken::default();
    let job = CancellationScope::new(Some(request.clone()));
    let nested = CancellationScope::new(Some(job.token()));
    let result = {
        let _guard = CancellationGuard::new(Some(nested.token()));
        let canceller = std::thread::spawn(move || {
            std::thread::sleep(HEAD_START);
            request.request_cancel();
            Instant::now()
        });
        let result = h.unify(&[wide_sums()]);
        let returned = Instant::now();
        let latency = returned.saturating_duration_since(canceller.join().unwrap());
        assert!(latency < PROMPT, "returned {latency:?} after the request");
        result
    };
    assert!(matches!(result, Err(MaudeError::Cancelled)), "{result:?}");
    h.check_backend_status().unwrap();
    assert_eq!(h.unify(&[small_sums()]).unwrap().len(), 7);
}

/// Two cases of one ordered search share a native-only handle. The first is
/// solved while the second, which a sequential search would never start, is
/// inside a runaway unification. The search returns the first case alone and
/// promptly; the cancelled call is neither stored nor a failure of the
/// session, and the handle answers on.
#[test]
fn a_solved_case_stops_a_later_case_inside_a_search_on_the_shared_handle() {
    use std::sync::atomic::{AtomicBool, Ordering};
    let h = naturals();
    let shared = h.clone();
    let entered = Arc::new(AtomicBool::new(false));
    let seen = entered.clone();
    let started = Instant::now();
    let results = workers(2)
        .install(move || {
            tamarin_utils::parallel::try_map_until(
                vec![0, 1],
                move |case| -> Result<usize, MaudeError> {
                    if case == 1 {
                        entered.store(true, Ordering::Release);
                        return Ok(shared.unify(&[wide_sums()])?.len());
                    }
                    // Solve only once the later case is inside its search.
                    let waiting = Instant::now();
                    while !entered.load(Ordering::Acquire) {
                        assert!(waiting.elapsed() < 4 * PROMPT, "no second worker");
                        std::thread::sleep(Duration::from_millis(5));
                    }
                    std::thread::sleep(HEAD_START);
                    Ok(shared.unify(&[small_sums()])?.len())
                },
                |unifiers| *unifiers == 7,
            )
        })
        .unwrap();
    let elapsed = started.elapsed();
    assert_eq!(results, [7]);
    assert!(seen.load(Ordering::Acquire));
    assert!(
        elapsed < HEAD_START + 2 * PROMPT,
        "returned after {elapsed:?}"
    );
    eprintln!("ordered search: returned {elapsed:?} after its start");
    h.check_backend_status().unwrap();
    // Only the solved case's unification was answered and counted.
    assert_eq!(h.stats().lean_unify_count, 1);
    assert_eq!(h.unify(&[small_sums()]).unwrap().len(), 7);
    assert_eq!(h.stats().lean_unify_count, 1);
}

/// What a job runs into after its request was cancelled is not the
/// session's failure: nothing is latched, and the job sees a cancellation.
#[test]
fn a_cancelled_job_does_not_fail_the_session() {
    let mut h = naturals();
    h.set_search_work(1 << 10);
    let token = CancellationToken::default();
    token.request_cancel();
    {
        let _guard = CancellationGuard::new(Some(token));
        let result = h.unify(&[wide_sums()]);
        assert!(matches!(result, Err(MaudeError::Cancelled)), "{result:?}");
        // An error the same job could only absorb.
        let lost: Result<bool, _> = Err(MaudeError::Other("lost".into()));
        assert!(!h.absorb(lost, || false));
    }
    h.check_backend_status().unwrap();
    // The same request from a live job is a failure of the session.
    assert!(h.unify(&[wide_sums()]).is_err());
    assert!(h.check_backend_status().is_err());
}

/// Jobs that share one native-only handle get the answers a sequential run
/// gets from a session of its own, whoever asks first and whichever of them
/// finds the memo filled.
#[test]
fn jobs_sharing_a_handle_get_the_answers_of_a_sequential_session() {
    let [x, y, z, w] = ["x", "y", "z", "w"].map(variable);
    let [a, b] = ["a", "b"].map(pub_term);
    let bag = |terms: &[&LNTerm]| {
        f_app_ac(
            AcSym::Union,
            terms.iter().map(|term| (*term).clone()).collect(),
        )
    };
    let queries: Vec<Equal<LNTerm>> = vec![
        Equal::new(bag(&[&x, &y]), bag(&[&z, &w])),
        Equal::new(bag(&[&x, &y]), bag(&[&a, &b])),
        Equal::new(bag(&[&x, &x, &y]), bag(&[&z, &a, &a])),
        Equal::new(bag(&[&x, &a]), bag(&[&y, &b])),
        Equal::new(bag(&[&x, &y, &z]), bag(&[&w, &a])),
        Equal::new(bag(&[&a, &b]), bag(&[&b, &a])),
        Equal::new(bag(&[&a, &x]), bag(&[&b, &b])),
    ];
    type Answer = (
        Vec<Vec<(LVar, LNTerm)>>,
        bool,
        Vec<Vec<(LVar, LNTerm)>>,
        LNTerm,
    );
    let ask = |h: &MaudeHandle, eq: &Equal<LNTerm>| -> Result<Answer, MaudeError> {
        let eqs = std::slice::from_ref(eq);
        Ok((
            h.unify(eqs)?,
            h.unifiable(eqs)?,
            h.match_eqs(eqs)?,
            h.reduce(&eq.lhs)?,
        ))
    };
    let sequential: Vec<Answer> = {
        let h = native();
        queries.iter().map(|eq| ask(&h, eq).unwrap()).collect()
    };
    let h = native();
    let shared = h.clone();
    // Every query from several jobs at once, in an order that differs
    // between the jobs.
    let jobs: Vec<(usize, Equal<LNTerm>)> = (0..8)
        .flat_map(|round| {
            let n = queries.len();
            let queries = queries.clone();
            (0..n).map(move |i| {
                let index = (i * (round + 1) + round) % n;
                (index, queries[index].clone())
            })
        })
        .collect();
    let parallel = workers(4)
        .install(move || {
            tamarin_utils::parallel::try_map(jobs, move |(index, eq)| {
                Ok::<_, MaudeError>((index, ask(&shared, &eq)?))
            })
        })
        .unwrap();
    assert_eq!(parallel.len(), 8 * queries.len());
    for (index, answer) in parallel {
        assert_eq!(answer, sequential[index], "query {index}");
    }
    h.check_backend_status().unwrap();
}
