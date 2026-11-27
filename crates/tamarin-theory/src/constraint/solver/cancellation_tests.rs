//! Test-only rendezvous during solver work. The gate pauses workers
//! before their next solver step; it neither installs nor checks cancellation.

use std::sync::{
    atomic::{AtomicUsize, Ordering},
    mpsc, Arc, Condvar, Mutex,
};
use std::time::Duration;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Work {
    Search,
    Sources,
    Terminal,
}

#[derive(Debug)]
pub(crate) struct WorkerGate {
    work: Work,
    participants: usize,
    entered: mpsc::Sender<std::thread::ThreadId>,
    entered_count: AtomicUsize,
    released: Mutex<bool>,
    ready: Condvar,
}

impl WorkerGate {
    pub(crate) fn new(
        work: Work,
        participants: usize,
    ) -> (Arc<Self>, mpsc::Receiver<std::thread::ThreadId>) {
        let (entered, receiver) = mpsc::channel();
        (
            Arc::new(Self {
                work,
                participants,
                entered,
                entered_count: AtomicUsize::new(0),
                released: Mutex::new(false),
                ready: Condvar::new(),
            }),
            receiver,
        )
    }

    pub(crate) fn release(&self) {
        *self.released.lock().unwrap() = true;
        self.ready.notify_all();
    }
}

pub(crate) fn checkpoint(ctx: &super::ProofContext, work: Work) {
    let gate = ctx.worker_gate.lock().unwrap().clone();
    let Some(gate) = gate else { return };
    if gate.work != work || gate.entered_count.fetch_add(1, Ordering::Relaxed) >= gate.participants
    {
        return;
    }
    gate.entered.send(std::thread::current().id()).unwrap();
    let (released, _) = gate
        .ready
        .wait_timeout_while(
            gate.released.lock().unwrap(),
            Duration::from_secs(10),
            |released| !*released,
        )
        .unwrap();
    assert!(*released, "test did not release the active solver worker");
}

/// How many of a session's pooled Maude processes a scheduling row holds
/// while the proof runs.
#[derive(Clone, Copy, Debug)]
enum Held {
    None,
    One,
    All,
}

/// Parallel proof search returns exactly the serial proof, however wide it
/// forks and however few Maude processes remain for the forked cases.  Rows
/// `(theory, lemma, threads, pool size, held processes, rendezvous)`: with
/// `rendezvous` k > 0, the first k search workers wait at the gate until all
/// k entered, so k distinct workers are active at once.  A parallel row
/// must fork at least once, and the serial baseline (one thread, no held
/// process) never forks.  rs_ref sees parallel output at one width only.
#[test]
fn parallel_search_matches_serial_search() {
    use crate::prove::{prove_lemma_in_session, ProverSession, ProverSessionOptions};
    use std::fmt::Write;

    // Gate and Work premises fork; as in HS, saturation applies the
    // [no_precomp] premises' sources, so the Step prefix collapses.  The
    // first case (A_Quick) supplies a counterexample or witness.
    let mut deep = String::from(
        "theory DeepFork begin\n\
         rule A_Quick: [] --[ Choice('a'), Seed(), Quick() ]-> [ Gate('x') ]\n\
         rule Z_Alternative: [ Work3('x')[no_precomp] ] --> [ Gate('x') ]\n\
         rule WorkBase: [] --[ Seed() ]-> [ Work0('x') ]\n",
    );
    for i in 1..=3 {
        for side in ["left", "right"] {
            let prev = i - 1;
            writeln!(deep, "rule Work{i}_{side}: [ Work{prev}('x')[no_precomp] ] --[ Choice('{side}') ]-> [ Work{i}('x') ]").unwrap();
        }
    }
    let mut previous = String::from("Gate");
    for i in 1..=36 {
        writeln!(
            deep,
            "rule Step{i}: [ {previous}('x')[no_precomp] ] --> [ Prefix{i}('x') ]"
        )
        .unwrap();
        previous = format!("Prefix{i}");
    }
    deep.push_str(
        "rule Finish: [ Prefix36('x')[no_precomp] ] --[ Attack() ]-> []\n\
         rule OuterA: [ Gate('x')[no_precomp] ] --[ Nested() ]-> []\n\
         rule OuterB: [] --[ Nested() ]-> []\n\
         lemma nested: exists-trace \"Ex #i. Nested()@i\"\n\
         lemma seeded: \"All #i. Attack()@i ==> (Ex #j. Seed()@j)\"\n\
         lemma no_attack: \"not (Ex #i. Attack()@i)\"\n\
         lemma later: exists-trace \"Ex #i. Attack()@i & not (Ex #j. Quick()@j)\"\n\
         lemma attack: exists-trace \"Ex #i. Attack()@i\"\nend",
    );
    // Four cases, only C without a missing premise: the witness comes late.
    let wide = "theory Wide begin
        rule A: [ Missing('a')[no_precomp] ] --[ End() ]-> []
        rule B: [ Missing('b')[no_precomp] ] --[ End() ]-> []
        rule C: [] --[ End() ]-> []
        rule D: [ Missing('d')[no_precomp] ] --[ End() ]-> []
        lemma witness: exists-trace \"Ex #i. End() @ i\"
        end";
    let rows: &[(&str, &str, usize, usize, Held, usize)] = &[
        (&deep, "no_attack", 2, 3, Held::None, 0),
        (&deep, "seeded", 2, 3, Held::None, 0),
        (&deep, "nested", 2, 3, Held::None, 0),
        (&deep, "later", 2, 3, Held::None, 0),
        (&deep, "attack", 2, 3, Held::None, 0),
        (&deep, "later", 2, 3, Held::All, 0),
        (&deep, "seeded", 2, 3, Held::All, 0),
        (wide, "witness", 4, 2, Held::One, 2),
    ];
    let Some(path) = tamarin_test_support::require_maude_path() else {
        return;
    };
    let sig = tamarin_term::maude_sig::pair_maude_sig();
    for (source, lemma, threads, pool_size, held, rendezvous) in rows {
        let label = format!("{lemma} on {threads} threads, pool {pool_size}, held {held:?}");
        let maude = tamarin_term::maude_proc::MaudeHandle::start(&path, sig.clone()).unwrap();
        let parsed = tamarin_parser::parse_theory(source, &[]).unwrap();
        let elaborated = crate::elaborate::elaborate(&parsed).unwrap();
        let (theory, _) = crate::closed_theory::close_theory(elaborated, &maude, None).unwrap();
        let pool = tamarin_term::maude_proc::MaudePool::new(
            &path,
            sig.clone(),
            *pool_size,
            Default::default(),
        );
        let options = ProverSessionOptions {
            maude_pool: Some(Arc::new(pool.unwrap())),
            ..Default::default()
        };
        let session = ProverSession::build(&theory, maude, options).unwrap();
        let ctx = session.template_context();
        let prove = |threads: usize| {
            let workers = rayon::ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .unwrap();
            let proof = workers
                .install(|| prove_lemma_in_session(&session, lemma, usize::MAX))
                .unwrap();
            let status = crate::constraint::solver::search::proof_status(&proof);
            (status, crate::pretty_theory::pretty_proof_body(&proof))
        };
        let observe = |participants| {
            let (gate, entered) = WorkerGate::new(Work::Search, participants);
            *ctx.worker_gate.lock().unwrap() = Some(gate.clone());
            (gate, entered)
        };

        let (gate, entered) = observe(usize::MAX);
        gate.release();
        let serial = prove(1);
        assert_eq!(
            entered.try_iter().count(),
            0,
            "{label}: a lone worker stays serial"
        );

        let maudes = ctx.maude_pool.as_ref().unwrap();
        let holding = match held {
            Held::None => 0,
            Held::One => 1,
            Held::All => maudes.size(),
        };
        let _held: Vec<_> = (0..holding).map(|_| maudes.acquire()).collect();
        let parallel = if *rendezvous == 0 {
            let (gate, entered) = observe(usize::MAX);
            gate.release();
            let parallel = prove(*threads);
            assert!(entered.try_iter().count() > 0, "{label}: no fork");
            parallel
        } else {
            let (gate, entered) = observe(*rendezvous);
            std::thread::scope(|scope| {
                let proof = scope.spawn(|| prove(*threads));
                let wait = Duration::from_secs(5);
                let ids: std::collections::BTreeSet<_> = (0..*rendezvous)
                    .map(|_| format!("{:?}", entered.recv_timeout(wait).unwrap()))
                    .collect();
                gate.release();
                assert_eq!(ids.len(), *rendezvous, "{label}: distinct workers");
                proof.join().unwrap()
            })
        };
        *ctx.worker_gate.lock().unwrap() = None;
        assert_eq!(parallel, serial, "{label}");
    }
}
