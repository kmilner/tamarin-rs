//! Parallel work with scoped cancellation and ordered speculative results.
//!
//! Contract for work closures:
//!
//! * A job may run on any pool thread, including on the stack of a thread
//!   that is waiting for a map or [`SharedOnce`] and helps meanwhile. It
//!   inherits only the cancellation token. It must install
//!   every other thread-local it reads and restore the previous value before
//!   returning.
//! * A job must not block in a plain Rayon `join`, `scope` or parallel
//!   iterator. While blocked there, Rayon may run an unrelated job on that
//!   stack, which can deadlock if this job owns a [`SharedOnce`] build.
//! * Blocking operations must poll `cancellation::check` or register with
//!   `on_cancel`. Waits in this module wake through `on_cancel`, so they
//!   need `CancellationToken::cancel`, not only `request_cancel`.

use crate::cancellation::{
    self, CancellationGuard, CancellationScope, CancellationToken, Cancelled,
};
use std::cell::RefCell;
use std::collections::VecDeque;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

thread_local! {
    static CURRENT_GROUP: RefCell<Option<Arc<Group>>> = const { RefCell::new(None) };
    // A worker can finish many maps without returning to Rayon's event loop.
    // Reuse its dispatch queue across maps instead of queuing a wrapper per job.
    static DISPATCHER: Arc<Dispatcher> = Arc::new(Dispatcher::default());
}

type Job = Box<dyn FnOnce() + Send>;

struct Batch {
    group: Arc<Group>,
    jobs: std::vec::IntoIter<Job>,
}

struct Group {
    token: CancellationToken,
    panic: Mutex<Option<Box<dyn std::any::Any + Send>>>,
    parent: Option<Arc<Group>>,
    dispatcher: Arc<Dispatcher>,
    remaining: AtomicUsize,
    /// Items not yet visited. The group's jobs are lanes that can each visit
    /// several of them.
    items: AtomicUsize,
}

impl Group {
    fn new(
        parent: Option<Arc<Group>>,
        token: CancellationToken,
        remaining: usize,
        items: usize,
    ) -> Arc<Self> {
        let dispatcher = parent
            .as_ref()
            .map_or_else(|| DISPATCHER.with(Arc::clone), |g| g.dispatcher.clone());
        Arc::new(Self {
            token,
            panic: Mutex::default(),
            parent,
            dispatcher,
            remaining: AtomicUsize::new(remaining),
            items: AtomicUsize::new(items),
        })
    }

    fn current_member() -> Option<Arc<Self>> {
        let token = cancellation::current()?;
        CURRENT_GROUP.with(|cell| {
            cell.borrow()
                .as_ref()
                .filter(|group| token.descends_from(&group.token))
                .cloned()
        })
    }

    fn root(&self) -> &Self {
        std::iter::successors(Some(self), |g| g.parent.as_deref())
            .last()
            .unwrap()
    }

    fn job(self: &Arc<Self>, work: impl FnOnce() + Send + 'static) -> Job {
        let group = self.clone();
        Box::new(move || {
            let _current = GroupGuard::new(group.clone());
            let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let _panic = CancelOnPanic(&group.token);
                work();
            }));
            if let Err(panic) = outcome {
                group.panic.lock().unwrap().get_or_insert(panic);
            }
            group.finish_item();
        })
    }

    fn join(&self) {
        self.dispatcher
            .wait(self, true, None)
            .expect("unconditional join");
        if let Some(panic) = self.panic.lock().unwrap().take() {
            std::panic::resume_unwind(panic);
        }
    }

    fn finish_item(&self) {
        if self.remaining.fetch_sub(1, Ordering::AcqRel) == 1 {
            let _state = self.dispatcher.state.lock();
            self.dispatcher.changed.notify_all();
        }
    }

    fn descends_from(&self, ancestor: &Group) -> bool {
        std::iter::successors(Some(self), |group| group.parent.as_deref())
            .any(|group| std::ptr::eq(group, ancestor))
    }
}

/// Number of enclosing parallel maps that still have another outstanding item.
pub fn active_split_depth() -> usize {
    CURRENT_GROUP.with(|cell| {
        let current = cell.borrow();
        std::iter::successors(current.as_deref(), |group| group.parent.as_deref())
            .filter(|group| group.items.load(Ordering::Relaxed) > 1)
            .count()
    })
}

#[derive(Default)]
struct DispatchState {
    ready: VecDeque<Batch>,
    scheduled: usize,
}

impl DispatchState {
    fn take(&mut self, index: usize) -> Job {
        let jobs = &mut self.ready[index].jobs;
        let job = jobs.next().expect("only nonempty batches are queued");
        if jobs.len() == 0 {
            self.ready.remove(index);
        }
        job
    }
}

#[derive(Default)]
struct Dispatcher {
    state: parking_lot::Mutex<DispatchState>,
    changed: parking_lot::Condvar,
}

impl Dispatcher {
    fn submit(self: &Arc<Self>, batch: Batch) {
        let spawn = {
            let mut state = self.state.lock();
            let spawn = batch
                .jobs
                .len()
                .min(rayon::current_num_threads().saturating_sub(state.scheduled));
            state.ready.push_back(batch);
            self.changed.notify_all();
            state.scheduled += spawn;
            spawn
        };
        for _ in 0..spawn {
            let dispatcher = self.clone();
            rayon::spawn(move || dispatcher.drain());
        }
    }

    fn drain(self: Arc<Self>) {
        loop {
            let job = {
                let mut state = self.state.lock();
                if state.ready.is_empty() {
                    state.scheduled -= 1;
                    return;
                }
                state.take(0)
            };
            job();
        }
    }

    fn wait(
        &self,
        group: &Group,
        help: bool,
        cancel: Option<&CancellationToken>,
    ) -> Result<(), Cancelled> {
        // Registered before the state lock: a cancelled token runs it at once.
        let _wake = cancel.map(|token| {
            let dispatcher = group.dispatcher.clone();
            token.on_cancel(move || {
                let _state = dispatcher.state.lock();
                dispatcher.changed.notify_all();
            })
        });
        let mut state = self.state.lock();
        while group.remaining.load(Ordering::Acquire) != 0 {
            if let Some(token) = cancel {
                token.check()?;
            }
            if help
                && let Some(i) = state
                    .ready
                    .iter()
                    .position(|batch| batch.group.descends_from(group))
            {
                let job = state.take(i);
                drop(state);
                job();
                state = self.state.lock();
            } else {
                self.changed.wait(&mut state);
            }
        }
        Ok(())
    }
}

struct GroupGuard(Option<Arc<Group>>);
impl GroupGuard {
    fn new(group: Arc<Group>) -> Self {
        Self(CURRENT_GROUP.with(|cell| cell.replace(Some(group))))
    }
}
impl Drop for GroupGuard {
    fn drop(&mut self) {
        CURRENT_GROUP.with(|cell| cell.replace(self.0.take()));
    }
}

/// A fallible lazy value shared by workers. Within one work tree, waiters
/// can run the initializer's descendant jobs. Other requests wait cancellably.
/// A failed or cancelled initializer is not cached: the next caller retries
/// with its own initializer, so a build owned by a speculative branch that
/// gets cut is restarted by a branch that still needs the value.
/// A cancelled waiter that is running a borrowed job leaves only once that
/// job returns.
pub struct SharedOnce<T> {
    value: std::sync::OnceLock<T>,
    owner: parking_lot::Mutex<Option<Arc<Group>>>,
}

impl<T> Default for SharedOnce<T> {
    fn default() -> Self {
        Self {
            value: Default::default(),
            owner: Default::default(),
        }
    }
}

impl<T> std::fmt::Debug for SharedOnce<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SharedOnce")
            .field("initialized", &self.get().is_some())
            .finish()
    }
}

impl<T> From<T> for SharedOnce<T> {
    fn from(value: T) -> Self {
        Self {
            value: value.into(),
            owner: Default::default(),
        }
    }
}

impl<T> SharedOnce<T> {
    pub fn get(&self) -> Option<&T> {
        self.value.get()
    }

    pub fn get_or_try_init<E: From<Cancelled>>(
        &self,
        init: impl FnOnce() -> Result<T, E>,
    ) -> Result<&T, E> {
        let token = cancellation::current();
        let map = Group::current_member();
        loop {
            cancellation::check()?;
            let mut owner = self.owner.lock();
            if let Some(value) = self.get() {
                return Ok(value);
            }
            if let Some(group) = owner.clone() {
                drop(owner);
                assert!(
                    !map.as_deref()
                        .is_some_and(|waiter| waiter.descends_from(&group)),
                    "SharedOnce initializer depends on its own value"
                );
                let help = map
                    .as_deref()
                    .zip(group.parent.as_deref())
                    .is_some_and(|(waiter, builder)| std::ptr::eq(waiter.root(), builder.root()));
                group.dispatcher.wait(&group, help, token.as_ref())?;
                continue;
            }
            let attempt = CancellationScope::new(token.clone());
            let group = Group::new(map.clone(), attempt.token(), 1, 1);
            *owner = Some(group.clone());
            drop(owner);

            struct Release<'a>(&'a parking_lot::Mutex<Option<Arc<Group>>>);
            impl Drop for Release<'_> {
                fn drop(&mut self) {
                    self.0.lock().take().unwrap().finish_item();
                }
            }
            let _release = Release(&self.owner);
            let value = {
                let _group = GroupGuard::new(group);
                let _guard = CancellationGuard::new(Some(attempt.token()));
                init()
            };
            cancellation::check()?;
            let value = value?;
            return Ok(self.value.get_or_init(|| value));
        }
    }
}

/// Cancel queued owned work without waiting for its executor to admit it.
/// Once admitted, wait for completion so no worker outlives its caller's
/// cleanup.
fn run_cancellable_job<R: Send + 'static, E: From<Cancelled> + Send + 'static>(
    submit: impl FnOnce(Box<dyn FnOnce() + Send>),
    f: impl FnOnce() -> Result<R, E> + Send + 'static,
) -> Result<R, E> {
    use std::sync::{mpsc, Arc, Mutex};
    cancellation::check()?;
    let token = cancellation::current();
    // Taking the closure is the admission decision: exactly one of the
    // caller cancelling it and a worker starting it can acquire its payload.
    let pending = Arc::new(Mutex::new(Some(f)));
    let worker_pending = pending.clone();
    enum Event<T> {
        Finished(std::thread::Result<T>),
        Cancelled,
    }
    let (events, received) = mpsc::channel();
    let cancelled = events.clone();
    let _wake = token.as_ref().map(|token| {
        token.on_cancel(move || {
            let _ = cancelled.send(Event::Cancelled);
        })
    });
    submit(Box::new(move || {
        let work = worker_pending.lock().unwrap().take();
        let Some(work) = work else { return };
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _guard = CancellationGuard::new(token);
            cancellation::check()?;
            work()
        }));
        let _ = events.send(Event::Finished(outcome));
    }));
    loop {
        match received.recv().expect("worker lost its result") {
            Event::Finished(Ok(outcome)) => {
                cancellation::check()?;
                return outcome;
            }
            Event::Finished(Err(panic)) => std::panic::resume_unwind(panic),
            Event::Cancelled => {
                // Drop the withdrawn closure only after releasing the lock.
                let withdrawn = pending.lock().unwrap().take();
                if withdrawn.is_some() {
                    return Err(Cancelled.into());
                }
                // Already running: its token stops the solver/I/O, and
                // the result channel acknowledges actual worker cleanup.
            }
        }
    }
}

/// Run `work` on a Rayon worker. A caller outside the pool can withdraw the
/// job while it is still queued.
pub fn in_pool<R, E>(work: impl FnOnce() -> Result<R, E> + Send + 'static) -> Result<R, E>
where
    R: Send + 'static,
    E: From<Cancelled> + Send + 'static,
{
    if rayon::current_thread_index().is_none() {
        run_cancellable_job(rayon::spawn, work)
    } else {
        work()
    }
}

/// Like [`in_pool`], but a caller without a cancellation token keeps the work
/// on its own thread.
pub fn with_worker<R, E>(work: impl FnOnce() -> Result<R, E> + Send + 'static) -> Result<R, E>
where
    R: Send + 'static,
    E: From<Cancelled> + Send + 'static,
{
    cancellation::check()?;
    if cancellation::current().is_some() {
        in_pool(work)
    } else {
        work()
    }
}

/// Like an indexed parallel `map` followed by `collect::<Result<Vec<_>, _>>()`,
/// but a failed task stops its siblings, including their blocking subprocesses.
/// Keep the originating error: cancellation errors from siblings must not mask it.
/// When several tasks fail on their own, the first to fail in time is reported,
/// so which one can vary between runs; [`try_map_until`] reports in input order.
/// All admitted work is joined before returning; successful values retain input
/// order. Tasks must observe `cancellation::check` or register their blocking I/O.
///
/// Cancellation is local to this operation. An enclosing request can cancel it,
/// but a local failure does not cancel that request or poison a subsequent retry.
/// Nested maps keep using the worker pool. Work must not introduce independent
/// Rayon joins, which could steal a blocked ancestor's sibling.
///
/// Inputs must already be materialized. Accepting a parallel iterator would
/// allow upstream adapters to panic before our task guard can cancel siblings.
/// Put fallible or panicking computation in `work`, inside that guard.
///
/// ```compile_fail
/// use rayon::prelude::*;
/// use tamarin_utils::{cancellation::Cancelled, parallel::try_map};
/// let input = (0..2).into_par_iter().map(|i| if i == 1 { panic!() } else { i });
/// let _ = try_map(input, Ok::<_, Cancelled>);
/// ```
pub fn try_map<I, F, T, E>(items: Vec<I>, work: F) -> Result<Vec<T>, E>
where
    I: Send + 'static,
    F: Fn(I) -> Result<T, E> + Sync + Send + 'static,
    T: Send + 'static,
    E: From<Cancelled> + Send + 'static,
{
    try_map_with_helpers(items, no_helper, move |_, item| work(item))
}

/// Map independent CPU computations in input order, including inside a nested group.
pub fn map_independent<I: Send + 'static, T: Send + 'static>(
    items: Vec<I>,
    work: impl Fn(I) -> T + Sync + Send + 'static,
) -> Result<Vec<T>, Cancelled> {
    try_map(items, move |item| Ok(work(item)))
}

/// What a helper lane brings to the items it visits.
pub enum Helper<W> {
    /// A resource of its own, passed to the work.
    Own(W),
    /// Nothing: the work uses what the caller has, as the primary lane does.
    Shared,
}

fn no_helper() -> Option<Helper<()>> {
    Some(Helper::Shared)
}

/// Like [`try_map`], with a primary worker and optional helpers.
/// The caller's lane takes item zero and then further items, and calls
/// `work(None, item)`. Before claiming each item a helper lane calls
/// `acquire`: with a resource of its own it calls `work(Some(resource), item)`
/// and returns the resource afterwards, with [`Helper::Shared`] it works as
/// the caller's lane does, and with `None` it leaves. Acquisition may start
/// a resource under the installed cancellation token.
pub fn try_map_with_helpers<I, W, T, E>(
    items: Vec<I>,
    acquire: impl Fn() -> Option<Helper<W>> + Sync + Send + 'static,
    work: impl Fn(Option<W>, I) -> Result<T, E> + Sync + Send + 'static,
) -> Result<Vec<T>, E>
where
    I: Send + 'static,
    W: Send + 'static,
    T: Send + 'static,
    E: From<Cancelled> + Send + 'static,
{
    cancellation::check()?;
    let scope = CancellationScope::new(cancellation::current());
    let token = scope.token();
    let error = Arc::new(Mutex::new(None));
    let worker_error = error.clone();
    let worker_token = token.clone();
    let visit = move |worker: Option<W>, item| {
        let token = &worker_token;
        let _guard = CancellationGuard::new(Some(token.clone()));
        cancellation::check()?;
        match work(worker, item) {
            Ok(value) => Ok(value),
            Err(failure) => {
                // Publish before waking cancelled siblings. Do not hold the
                // error lock while callbacks stop their blocking operations.
                let mut first = worker_error.lock().unwrap();
                if first.is_none() {
                    *first = Some(failure);
                }
                drop(first);
                token.cancel();
                Err(Cancelled)
            }
        }
    };
    let admission = CancellationScope::new(Some(token.clone()));
    let results = lane_map(items, token, admission, acquire, move |worker, _, item| {
        Some(visit(worker, item))
    })?
    .into_iter()
    // A failure stops the lanes before they claim the remaining items.
    .map(|result| result.unwrap_or(Err(Cancelled)));
    // An enclosing request cancellation takes precedence over incidental I/O
    // errors from killed children. Our local token never cancels that request.
    cancellation::check()?;
    let failure = error.lock().unwrap().take();
    match failure {
        Some(error) => Err(error),
        None => results.collect::<Result<Vec<_>, _>>().map_err(E::from),
    }
}

/// Evaluate an ordered prefix, stopping at the first error or value satisfying
/// `stop`, just as a sequential traversal would. Later speculative results may
/// finish first, but must never cancel an earlier task or change its outcome.
/// A terminal result cancels only its suffix; all started work is joined before
/// returning. Thus a required error cannot be trapped behind unbounded *later*
/// work, while an earlier solution can still supersede a speculative error.
/// Owns its inputs and closures so nested calls can keep using the worker pool
/// without entering a Rayon join. Waiting callers help only their descendants.
/// A cancellable caller outside Rayon can withdraw the job before pool entry.
/// Work must not introduce independent Rayon joins, which could steal a blocked
/// ancestor's sibling. Scheduling fairness across independent roots is not
/// guaranteed.
/// All user work and its captures finish before returning. A map and its
/// descendants share one ready queue with one entry per pending batch. At most
/// N reusable dispatch tasks per originating worker can remain queued in an
/// N-worker Rayon pool (at most N² across that pool).
/// Like [`try_map`], accepts only materialized inputs so all user computation
/// runs inside the task's cancellation-on-panic guard (including `stop`).
///
/// ```compile_fail
/// use rayon::prelude::*;
/// use tamarin_utils::{cancellation::Cancelled, parallel::try_map_until};
/// let input = (0..2).into_par_iter().map(|i| if i == 1 { panic!() } else { i });
/// let _ = try_map_until(input, Ok::<_, Cancelled>, |_| false);
/// ```
///
/// # Panics
///
/// A panic in `work` or `stop` propagates after all started work finishes,
/// even if the panicking task belongs to a discarded suffix.
pub fn try_map_until<I, F, P, T, E>(items: Vec<I>, work: F, stop: P) -> Result<Vec<T>, E>
where
    I: Send + 'static,
    F: Fn(I) -> Result<T, E> + Sync + Send + 'static,
    P: Fn(&T) -> bool + Sync + Send + 'static,
    T: Send + 'static,
    E: From<Cancelled> + Send + 'static,
{
    try_map_until_with_helpers(items, no_helper, move |_, item| work(item), stop)
}

// One map in progress. Its lanes claim the items in order. Only the primary
// lane has a reserved item; a helper claims the next one once it knows what
// it brings.
struct LaneMap<I, A, V, T> {
    admission: CancellationScope,
    pending: Mutex<std::iter::Enumerate<std::vec::IntoIter<I>>>,
    results: Mutex<Vec<Option<T>>>,
    group: Arc<Group>,
    acquire: A,
    visit: V,
}

impl<I, A, V, T, W> LaneMap<I, A, V, T>
where
    I: Send + 'static,
    A: Fn() -> Option<Helper<W>> + Send + Sync + 'static,
    V: Fn(Option<W>, usize, I) -> Option<T> + Send + Sync + 'static,
    T: Send + 'static,
{
    fn run(self: &Arc<Self>, mut first: Option<(usize, I)>) {
        let primary = first.is_some();
        while first.is_some() || !self.admission.token().is_cancelled() {
            // A cancelled job that picked this lane up while waiting for a
            // value must not be kept here by another job's items.
            if !primary && cancellation::check().is_err() {
                return self.hand_back();
            }
            let lease = if primary {
                None
            } else {
                let helper = {
                    let _guard = CancellationGuard::new(Some(self.admission.token()));
                    (self.acquire)()
                };
                // Starting a resource can take a while.
                if cancellation::check().is_err() {
                    drop(helper);
                    return self.hand_back();
                }
                match helper {
                    Some(Helper::Own(resource)) => Some(resource),
                    Some(Helper::Shared) => None,
                    // The other lanes visit what is left.
                    None => return,
                }
            };
            let (next, pending) = {
                let mut queue = self.pending.lock().unwrap();
                (first.take().or_else(|| queue.next()), queue.len())
            };
            let Some((index, item)) = next else { break };
            // Stop helpers that are still starting a resource nobody needs.
            if pending == 0 {
                self.admission.token().cancel();
            }
            let Some(result) = (self.visit)(lease, index, item) else {
                self.group.items.fetch_sub(1, Ordering::Relaxed);
                break;
            };
            self.results.lock().unwrap()[index] = Some(result);
            self.group.items.fetch_sub(1, Ordering::Relaxed);
        }
        // Nobody will visit what is left. Drop it inside this job's panic
        // guard, and not while holding the queue.
        let skipped: Vec<_> = self.pending.lock().unwrap().by_ref().collect();
        self.group.items.fetch_sub(skipped.len(), Ordering::Relaxed);
        drop(skipped);
    }

    /// Queue this lane again for another worker.
    fn hand_back(self: &Arc<Self>) {
        if self.pending.lock().unwrap().len() == 0 {
            return;
        }
        // The job that is ending here still counts until it returns.
        self.group.remaining.fetch_add(1, Ordering::AcqRel);
        let lane = self.clone();
        let job = self.group.job(move || lane.run(None));
        self.group.dispatcher.submit(Batch {
            group: self.group.clone(),
            jobs: vec![job].into_iter(),
        });
    }
}

// Both fail-fast and ordered maps run here, with up to one lane per worker.
// The caller runs the primary lane and then waits. While it waits it may only
// run lanes of its own group and that group's descendants, even when another
// request shares the pool. Cancelling `admission` stops lanes from acquiring
// resources or claiming further items. An item that `visit` declines ends its
// lane, and its slot stays empty.
fn lane_map<I, W, T>(
    items: Vec<I>,
    token: CancellationToken,
    admission: CancellationScope,
    acquire: impl Fn() -> Option<Helper<W>> + Send + Sync + 'static,
    visit: impl Fn(Option<W>, usize, I) -> Option<T> + Send + Sync + 'static,
) -> Result<Vec<Option<T>>, Cancelled>
where
    I: Send + 'static,
    W: Send + 'static,
    T: Send + 'static,
{
    let count = items.len();
    let lanes = count.min(rayon::current_num_threads());
    if lanes < 2 {
        let _panic = CancelOnPanic(&token);
        let mut results: Vec<Option<T>> = (0..count).map(|_| None).collect();
        for (index, item) in items.into_iter().enumerate() {
            let Some(result) = visit(None, index, item) else {
                break;
            };
            results[index] = Some(result);
        }
        return Ok(results);
    }
    if rayon::current_thread_index().is_none() {
        return in_pool(move || lane_map(items, token, admission, acquire, visit));
    }
    let mut items = items.into_iter().enumerate();
    let first = items.next();
    let group = Group::new(Group::current_member(), token, lanes, count);
    let map = Arc::new(LaneMap {
        group: group.clone(),
        admission,
        pending: Mutex::new(items),
        results: Mutex::new((0..count).map(|_| None).collect()),
        acquire,
        visit,
    });
    let jobs = (1..lanes)
        .map(|_| {
            let helper = map.clone();
            group.job(move || helper.run(None))
        })
        .collect::<Vec<_>>()
        .into_iter();
    group.dispatcher.submit(Batch {
        group: group.clone(),
        jobs,
    });
    let primary = map.clone();
    group.job(move || primary.run(first))();
    // All user work has finished before errors or panics leave this operation.
    // Only bounded dispatcher tasks can remain queued in Rayon.
    group.join();
    Ok(std::mem::take(&mut *map.results.lock().unwrap()))
}

/// Evaluate an ordered prefix with a primary worker and optional helpers.
/// The caller's lane takes item zero and then further items, and calls
/// `work(None, item)`. Before claiming each item a helper lane calls
/// `acquire`: with a resource of its own it calls `work(Some(resource), item)`
/// and returns the resource afterwards, with [`Helper::Shared`] it works as
/// the caller's lane does, and with `None` it leaves. Acquisition may start
/// a resource under the installed cancellation token.
pub fn try_map_until_with_helpers<I, W, T, E>(
    items: Vec<I>,
    acquire: impl Fn() -> Option<Helper<W>> + Send + Sync + 'static,
    work: impl Fn(Option<W>, I) -> Result<T, E> + Sync + Send + 'static,
    stop: impl Fn(&T) -> bool + Sync + Send + 'static,
) -> Result<Vec<T>, E>
where
    I: Send + 'static,
    W: Send + 'static,
    T: Send + 'static,
    E: From<Cancelled> + Send + 'static,
{
    cancellation::check()?;
    let scope = CancellationScope::new(cancellation::current());
    let token = scope.token();
    let children: Vec<_> = (0..items.len())
        .map(|_| CancellationScope::new(Some(token.clone())))
        .collect();
    let end = Arc::new(AtomicUsize::new(children.len()));
    let admission = CancellationScope::new(Some(token.clone()));
    let stop_admission = admission.token();
    let worker_end = end.clone();
    let visit = move |worker: Option<W>, index: usize, item| {
        let end = &worker_end;
        let _guard = CancellationGuard::new(Some(children[index].token()));
        if index > end.load(Ordering::Relaxed) || cancellation::check().is_err() {
            return None;
        }
        let result = work(worker, item);
        if match &result {
            Ok(value) => stop(value),
            Err(_) => true,
        } {
            let previous = end.fetch_min(index, Ordering::Relaxed);
            if index < previous {
                stop_admission.cancel();
                // Do not hold a result lock while subprocess cleanup executes.
                // Earlier tasks stay live even if a later task fails first.
                // Cancel through the previous cutoff, inclusive. That task
                // handles cancellation of the suffix beyond its own index.
                let suffix_end = previous.saturating_add(1).min(children.len());
                for child in &children[index + 1..suffix_end] {
                    child.token().cancel();
                }
            }
        }
        Some(result)
    };
    let results = lane_map(items, token, admission, acquire, visit)?;
    cancellation::check()?;
    results
        .into_iter()
        .take(end.load(Ordering::Relaxed).saturating_add(1))
        .map(|result| result.expect("required prefix was not cancelled"))
        .collect()
}

struct CancelOnPanic<'a>(&'a CancellationToken);
impl Drop for CancelOnPanic<'_> {
    fn drop(&mut self) {
        if std::thread::panicking() {
            self.0.cancel();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::mpsc;
    use std::time::Duration;

    #[derive(Debug, PartialEq, Eq)]
    enum Error {
        Cancelled,
        Failed,
    }
    impl From<Cancelled> for Error {
        fn from(_: Cancelled) -> Self {
            Self::Cancelled
        }
    }

    fn pool() -> rayon::ThreadPool {
        rayon::ThreadPoolBuilder::new()
            .num_threads(2)
            .build()
            .unwrap()
    }

    // A cancellable operation which cannot finish until its sibling fails.
    fn wait_for_cancellation(started: &mpsc::Sender<()>) -> Result<usize, Error> {
        let (cancelled, wait) = mpsc::channel();
        let _registration = cancellation::current().unwrap().on_cancel(move || {
            cancelled.send(()).unwrap();
        });
        started.send(()).unwrap();
        wait.recv_timeout(Duration::from_secs(10)).unwrap();
        cancellation::check()?;
        panic!("callback fired without cancellation");
    }
    #[test]
    fn a_helper_that_leaves_does_not_take_the_remaining_items_with_it() {
        let result = pool().install(|| {
            try_map_until_with_helpers(
                (0..50).collect(),
                || None::<Helper<()>>,
                |_, item: usize| {
                    std::thread::sleep(Duration::from_millis(1));
                    Ok::<_, Error>(item)
                },
                |_| false,
            )
        });
        assert_eq!(result, Ok((0..50).collect()));
    }

    #[test]
    fn a_stopped_map_no_longer_counts_as_split() {
        let depth = pool().install(|| {
            try_map_until(
                vec![0, 1, 2, 3],
                |index| {
                    if index != 0 {
                        return Ok::<_, Error>(usize::MAX);
                    }
                    let started = std::time::Instant::now();
                    while active_split_depth() > 0 && started.elapsed() < Duration::from_secs(5) {
                        std::thread::sleep(Duration::from_millis(1));
                    }
                    Ok(active_split_depth())
                },
                |depth| *depth == usize::MAX,
            )
        });
        assert_eq!(depth.unwrap()[0], 0);
    }

    #[test]
    fn a_cancelled_waiter_hands_a_borrowed_lane_back() {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(3)
            .build()
            .unwrap();
        let cell = Arc::new(SharedOnce::<usize>::default());
        let (helping, helped) = mpsc::channel::<()>();
        let helped = Mutex::new(helped);
        let waiter = Arc::new(Mutex::new(None));
        let unfinished_when_left = Arc::new(Mutex::new(None));
        let (shared, left) = (cell.clone(), unfinished_when_left.clone());
        let result = pool.install(move || {
            try_map_until(
                vec![0, 1, 2],
                move |index| match index {
                    0 => {
                        let (waiter, helping) = (waiter.clone(), Mutex::new(helping.clone()));
                        shared
                            .get_or_try_init(move || {
                                try_map((0..60).collect(), move |item: usize| {
                                    // The build does not get ahead of the waiter.
                                    let waiting = loop {
                                        match *waiter.lock().unwrap() {
                                            Some(waiting) => break waiting,
                                            None => std::thread::yield_now(),
                                        }
                                    };
                                    if std::thread::current().id() == waiting {
                                        let _ = helping.lock().unwrap().send(());
                                    }
                                    std::thread::sleep(Duration::from_millis(10));
                                    Ok::<_, Cancelled>(item)
                                })
                                .map(|items| items.into_iter().sum())
                            })
                            .copied()
                    }
                    // Stop the map once the waiter is running the builder's items.
                    1 => {
                        let helped = helped.lock().unwrap();
                        helped.recv_timeout(Duration::from_secs(10)).unwrap();
                        Ok(usize::MAX)
                    }
                    _ => {
                        *waiter.lock().unwrap() = Some(std::thread::current().id());
                        let value = shared.get_or_try_init(|| -> Result<_, Cancelled> {
                            panic!("the value is already being built")
                        });
                        *left.lock().unwrap() = Some(shared.get().is_none());
                        value.copied()
                    }
                },
                |value| *value == usize::MAX,
            )
        });
        assert_eq!(result, Ok(vec![(0..60).sum(), usize::MAX]));
        assert_eq!(*unfinished_when_left.lock().unwrap(), Some(true));
    }

    #[test]
    fn shared_once_retries_a_failed_initializer_and_caches_a_value() {
        let cell = SharedOnce::default();
        assert_eq!(
            cell.get_or_try_init(|| Err::<usize, _>(Error::Failed)),
            Err(Error::Failed)
        );
        assert_eq!(cell.get(), None);
        assert_eq!(cell.get_or_try_init(|| Ok::<_, Error>(7)), Ok(&7));
        assert_eq!(
            cell.get_or_try_init(|| -> Result<usize, Error> { panic!("already initialized") }),
            Ok(&7)
        );
    }

    #[test]
    fn shared_once_builds_once_for_contending_workers_of_one_tree() {
        let builds = Arc::new(AtomicUsize::new(0));
        let cell = Arc::new(SharedOnce::default());
        let values = pool().install(|| {
            let builds = builds.clone();
            try_map((0..8).collect(), move |_| {
                let builds = builds.clone();
                cell.get_or_try_init(move || {
                    builds.fetch_add(1, Ordering::SeqCst);
                    // The builder's own map needs the workers that are
                    // waiting for this value.
                    try_map((0..8).collect(), |i: usize| {
                        std::thread::sleep(Duration::from_millis(2));
                        Ok::<_, Error>(i)
                    })
                    .map(|parts| parts.into_iter().sum::<usize>())
                })
                .copied()
            })
        });
        assert_eq!(values, Ok(vec![28; 8]));
        assert_eq!(builds.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn a_shared_once_waiter_rebuilds_after_the_builder_is_cancelled() {
        let cell = Arc::new(SharedOnce::default());
        let (entered, started) = mpsc::channel();
        std::thread::scope(|scope| {
            let cell = &cell;
            let token = CancellationToken::default();
            let request = token.clone();
            let builder = scope.spawn(move || {
                let _guard = CancellationGuard::new(Some(request));
                cell.get_or_try_init(|| wait_for_cancellation(&entered))
                    .copied()
            });
            started.recv_timeout(Duration::from_secs(5)).unwrap();
            let waiter = scope.spawn(move || cell.get_or_try_init(|| Ok::<_, Error>(2)).copied());
            token.cancel();
            assert_eq!(builder.join().unwrap(), Err(Error::Cancelled));
            assert_eq!(waiter.join().unwrap(), Ok(2));
        });
        assert_eq!(cell.get(), Some(&2));
    }

    #[test]
    fn a_cancelled_shared_once_waiter_leaves_while_the_build_continues() {
        let cell = Arc::new(SharedOnce::default());
        let (entered, started) = mpsc::channel();
        let (release, blocked) = mpsc::channel::<()>();
        std::thread::scope(|scope| {
            let cell = &cell;
            let builder = scope.spawn(move || {
                cell.get_or_try_init(|| {
                    entered.send(()).unwrap();
                    blocked.recv_timeout(Duration::from_secs(10)).unwrap();
                    Ok::<_, Error>(1)
                })
                .copied()
            });
            started.recv_timeout(Duration::from_secs(5)).unwrap();
            let token = CancellationToken::default();
            let request = token.clone();
            let waiter = scope.spawn(move || {
                let _guard = CancellationGuard::new(Some(request));
                cell.get_or_try_init(|| -> Result<usize, Error> { panic!("second build") })
                    .copied()
            });
            token.cancel();
            assert_eq!(waiter.join().unwrap(), Err(Error::Cancelled));
            assert_eq!(cell.get(), None);
            release.send(()).unwrap();
            assert_eq!(builder.join().unwrap(), Ok(1));
        });
        assert_eq!(cell.get(), Some(&1));
    }

    #[test]
    fn cancelled_admission_retracts_queued_work_and_joins_started_work() {
        for admitted in [false, true] {
            let (submit, queued) = mpsc::channel();
            let (entered, started) = mpsc::channel();
            let (release, blocked) = mpsc::channel();
            let (finished, result) = mpsc::channel();
            let token = CancellationToken::default();
            let request = token.clone();
            std::thread::scope(|scope| {
                scope.spawn(move || {
                    let _guard = CancellationGuard::new(Some(request));
                    let outcome = run_cancellable_job(
                        |job| submit.send(job).unwrap(),
                        move || {
                            entered.send(()).unwrap();
                            blocked.recv_timeout(Duration::from_secs(5)).unwrap();
                            Ok::<_, Error>(())
                        },
                    );
                    finished.send(outcome).unwrap();
                });
                let job = queued.recv_timeout(Duration::from_secs(5)).unwrap();
                if admitted {
                    scope.spawn(job);
                    started.recv_timeout(Duration::from_secs(5)).unwrap();
                    token.cancel();
                    assert!(result.recv_timeout(Duration::from_millis(30)).is_err());
                    release.send(()).unwrap();
                } else {
                    token.cancel();
                    assert_eq!(
                        result.recv_timeout(Duration::from_secs(2)).unwrap(),
                        Err(Error::Cancelled)
                    );
                    job();
                    assert!(started.try_recv().is_err());
                    return;
                }
                assert_eq!(
                    result.recv_timeout(Duration::from_secs(2)).unwrap(),
                    Err(Error::Cancelled)
                );
            });
        }
    }

    #[test]
    fn admitted_panic_reaches_the_caller_and_restores_worker_state() {
        let pool = pool();
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _guard = CancellationGuard::new(Some(CancellationToken::default()));
            run_cancellable_job(
                |job| pool.spawn(job),
                || -> Result<(), Error> {
                    panic!("admitted job failed");
                },
            )
        }));
        assert!(panic.is_err());
        assert!(pool
            .broadcast(|_| cancellation::current().is_none())
            .into_iter()
            .all(|clear| clear));
    }

    #[test]
    fn failure_cancels_active_sibling_preserves_error_and_allows_retry() {
        let pool = pool();
        let parent = CancellationToken::default();
        pool.install(|| {
            let _guard = CancellationGuard::new(Some(parent.clone()));
            let (started, wait) = mpsc::channel();
            let wait = Mutex::new(wait);
            let result = try_map((0..2).collect(), move |i| {
                if i == 0 {
                    wait_for_cancellation(&started)
                } else {
                    wait.lock()
                        .unwrap()
                        .recv_timeout(Duration::from_secs(10))
                        .unwrap();
                    Err(Error::Failed)
                }
            });
            assert_eq!(result, Err(Error::Failed));
            assert!(!parent.is_cancelled());
            assert_eq!(
                try_map((0..8).collect(), Ok::<_, Error>),
                Ok((0..8).collect())
            );
        });
        assert!(pool
            .broadcast(|_| cancellation::current().is_none())
            .into_iter()
            .all(|v| v));
    }

    #[test]
    fn nested_failure_cancels_outer_sibling_without_losing_original_error() {
        let (started, wait) = mpsc::channel();
        let wait = Mutex::new(wait);
        let result = pool().install(|| {
            try_map((0..2).collect(), move |i| {
                if i == 0 {
                    wait_for_cancellation(&started)
                } else {
                    wait.lock()
                        .unwrap()
                        .recv_timeout(Duration::from_secs(10))
                        .unwrap();
                    try_map((0..1).collect(), |_| Err::<usize, _>(Error::Failed))?;
                    Ok(1)
                }
            })
        });
        assert_eq!(result, Err(Error::Failed));
    }

    #[test]
    fn cancelled_map_returns_while_unrelated_work_is_blocked() {
        let pool = pool();
        let token = CancellationToken::default();
        let worker_token = token.clone();
        let (done, result) = mpsc::channel();
        let (started, sibling) = mpsc::channel();
        let (queued, pending) = mpsc::channel();
        let (entered, unrelated) = mpsc::channel();
        let (release, blocked) = mpsc::channel::<()>();
        let blocked = Mutex::new(Some(blocked));
        let sibling = Mutex::new(sibling);
        pool.spawn(move || {
            let _guard = CancellationGuard::new(Some(worker_token));
            let outcome = try_map(vec![0, 1], move |item| {
                if item == 1 {
                    return wait_for_cancellation(&started);
                }
                sibling
                    .lock()
                    .unwrap()
                    .recv_timeout(Duration::from_secs(5))
                    .unwrap();
                let blocked = blocked.lock().unwrap().take().unwrap();
                let entered = entered.clone();
                rayon::spawn(move || {
                    let _ = entered.send(());
                    let _ = blocked.recv();
                });
                queued.send(()).unwrap();
                Ok(0)
            });
            let _ = done.send(outcome);
        });
        pending.recv_timeout(Duration::from_secs(5)).unwrap();
        // Give a coordinator using an unrestricted Rayon join a chance to
        // pick up the unrelated job before stopping its own remaining sibling.
        let _ = unrelated.recv_timeout(Duration::from_millis(100));
        token.cancel();
        let outcome = result.recv_timeout(Duration::from_secs(2));
        drop(release);
        assert_eq!(outcome, Ok(Err(Error::Cancelled)));
    }

    #[test]
    fn parent_cancellation_reaches_nested_work() {
        let parent = CancellationToken::default();
        let (started, wait) = mpsc::channel();
        let token = parent.clone();
        let worker = std::thread::spawn(move || {
            pool().install(|| {
                let _guard = CancellationGuard::new(Some(token));
                try_map((0..1).collect(), move |_| {
                    let started = started.clone();
                    try_map((0..1).collect(), move |_| wait_for_cancellation(&started))
                })
            })
        });
        wait.recv_timeout(Duration::from_secs(10)).unwrap();
        parent.cancel();
        assert_eq!(worker.join().unwrap(), Err(Error::Cancelled));
    }

    #[test]
    fn nested_work_can_use_workers_after_outer_tasks_have_started() {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(3)
            .build()
            .unwrap();
        let outer_started = std::sync::Barrier::new(2);
        let (started, wait) = mpsc::channel();
        let wait = Arc::new(Mutex::new(wait));
        pool.install(|| {
            try_map(vec![0, 1], move |outer| {
                outer_started.wait();
                if outer == 0 {
                    let started = started.clone();
                    let wait = wait.clone();
                    let workers = try_map(vec![0, 1], move |inner| {
                        let worker = std::thread::current().id();
                        if inner == 0 {
                            let other = wait
                                .lock()
                                .unwrap()
                                .recv_timeout(Duration::from_secs(10))
                                .expect("nested sibling must be able to start");
                            assert_ne!(worker, other);
                        } else {
                            started.send(worker).unwrap();
                        }
                        Ok::<_, Error>(worker)
                    })?;
                    assert_ne!(workers[0], workers[1]);
                }
                Ok::<_, Error>(())
            })
            .unwrap();
        });
        assert!(pool
            .broadcast(|_| CURRENT_GROUP.with(|group| group.borrow().is_none()))
            .into_iter()
            .all(|clear| clear));
    }

    #[test]
    fn waiting_caller_helps_descendants_in_a_saturated_pool() {
        let pool = pool();
        pool.install(|| {
            let caller = std::thread::current().id();
            let barrier = Arc::new(std::sync::Barrier::new(2));
            let results = try_map_until(
                vec![0, 1],
                move |_| {
                    barrier.wait();
                    if std::thread::current().id() == caller {
                        return Ok::<_, Error>(Vec::new());
                    }
                    let (send, receive) = mpsc::channel();
                    let receive = Mutex::new(receive);
                    try_map_until(
                        vec![0, 1],
                        move |index| {
                            assert_eq!(rayon::current_num_threads(), 2);
                            if index == 0 {
                                let other = receive
                                    .lock()
                                    .unwrap()
                                    .recv_timeout(Duration::from_secs(10))
                                    .expect("waiting parent must help its descendant");
                                assert_ne!(std::thread::current().id(), other);
                            } else {
                                send.send(std::thread::current().id()).unwrap();
                            }
                            Ok::<_, Error>(index)
                        },
                        |_| false,
                    )
                },
                |_| false,
            )
            .unwrap();
            assert_eq!(
                results.into_iter().flatten().collect::<Vec<_>>(),
                vec![0, 1]
            );
        });
        assert!(pool
            .broadcast(|_| CURRENT_GROUP.with(|cell| cell.borrow().is_none()))
            .into_iter()
            .all(|clear| clear));
    }

    // Called from a two-worker pool. Keep its other worker out of Rayon's
    // event loop until the sender signals that queued tasks may run.
    fn park_other_worker() -> mpsc::Sender<()> {
        let (started, start) = mpsc::channel();
        let (release, wait) = mpsc::channel();
        rayon::spawn(move || {
            started.send(()).unwrap();
            let _ = wait.recv_timeout(Duration::from_secs(10));
        });
        start.recv_timeout(Duration::from_secs(10)).unwrap();
        release
    }

    #[test]
    fn skipped_input_drop_panic_cancels_required_sibling() {
        struct Item(usize);
        impl Drop for Item {
            fn drop(&mut self) {
                if self.0 == 2 {
                    panic!("skipped input dropped");
                }
            }
        }
        let parent = CancellationToken::default();
        let token = parent.clone();
        let (done, finished) = mpsc::channel();
        let worker = std::thread::spawn(move || {
            let outcome = std::panic::catch_unwind(|| {
                pool().install(|| {
                    let _guard = CancellationGuard::new(Some(token));
                    let (started, start) = mpsc::channel();
                    let start = Mutex::new(start);
                    try_map_until(
                        vec![Item(0), Item(1), Item(2)],
                        move |item| {
                            match item.0 {
                                0 => {
                                    wait_for_cancellation(&started)?;
                                }
                                1 => {
                                    start
                                        .lock()
                                        .unwrap()
                                        .recv_timeout(Duration::from_secs(10))
                                        .unwrap();
                                }
                                _ => panic!("skipped input must not execute"),
                            }
                            Ok::<_, Error>(item.0)
                        },
                        |_| true,
                    )
                })
            });
            done.send(outcome.map_err(|panic| *panic.downcast::<&str>().unwrap()))
                .unwrap();
        });
        let outcome = finished.recv_timeout(Duration::from_secs(5));
        parent.cancel();
        worker.join().unwrap();
        assert_eq!(outcome, Ok(Err("skipped input dropped")));
    }

    #[test]
    fn completed_descendants_leave_no_ancestor_or_dispatch_backlog() {
        let pool = pool();
        pool.install(|| {
            let release = park_other_worker();
            let capture = Arc::new(());
            let weak = Arc::downgrade(&capture);
            try_map_until(
                vec![0, 1],
                move |outer| {
                    assert!(Arc::strong_count(&capture) >= 1);
                    if outer == 0 {
                        let group = CURRENT_GROUP.with(|cell| cell.borrow().clone().unwrap());
                        for _ in 0..5_000 {
                            assert_eq!(
                                try_map_until(vec![0, 1], Ok::<_, Error>, |_| false)?,
                                vec![0, 1]
                            );
                            // Only the unstarted outer sibling may remain queued.
                            let state = group.dispatcher.state.lock();
                            assert_eq!(state.ready.len(), 1);
                            assert_eq!(state.ready[0].jobs.len(), 1);
                            assert!(state.scheduled <= 2);
                        }
                    }
                    Ok::<_, Error>(outer)
                },
                |_| false,
            )
            .unwrap();
            DISPATCHER.with(|dispatcher| assert!(dispatcher.state.lock().ready.is_empty()));
            assert_eq!(pool.current_thread_has_pending_tasks(), Some(true));
            assert!(
                weak.upgrade().is_none(),
                "queued tasks retained work captures"
            );
            release.send(()).unwrap();
        });
    }

    #[test]
    fn queued_dispatchers_pick_up_new_work_after_reaching_the_limit() {
        let pool = pool();
        pool.install(|| {
            let release = park_other_worker();
            for _ in 0..100 {
                try_map_until(vec![0, 1], Ok::<_, Error>, |_| false).unwrap();
            }
            DISPATCHER.with(|dispatcher| assert_eq!(dispatcher.state.lock().scheduled, 2));
            let (other, finish) = mpsc::channel();
            let finish = Mutex::new(finish);
            let result = try_map_until(
                vec![0, 1],
                move |index| {
                    if index == 0 {
                        release.send(()).unwrap();
                        finish
                            .lock()
                            .unwrap()
                            .recv_timeout(Duration::from_secs(10))
                            .expect("an existing dispatcher must pick up newly submitted work");
                    } else {
                        other.send(()).unwrap();
                    }
                    Ok::<_, Error>(index)
                },
                |_| false,
            )
            .unwrap();
            assert_eq!(result, vec![0, 1]);
        });
    }

    #[test]
    fn speculative_error_cannot_override_earlier_solution() {
        let (failed, wait) = mpsc::channel();
        let wait = Mutex::new(wait);
        let result = pool().install(|| {
            try_map_until(
                (0..2).collect(),
                move |i| {
                    if i == 1 {
                        failed.send(()).unwrap();
                        Err(Error::Failed)
                    } else {
                        wait.lock()
                            .unwrap()
                            .recv_timeout(Duration::from_secs(10))
                            .unwrap();
                        cancellation::check()?;
                        Ok(i)
                    }
                },
                |_| true,
            )
        });
        assert_eq!(result, Ok(vec![0]));
    }

    #[test]
    fn available_worker_starts_a_third_item_and_earlier_failure_cancels_it() {
        let (started, third) = mpsc::channel();
        let third = Mutex::new(third);
        let result = pool().install(|| {
            try_map_until_with_helpers(
                vec![0, 1, 2],
                || Some(Helper::Own(())),
                move |lease, i| match i {
                    0 => {
                        assert!(lease.is_none(), "the primary owns the first item");
                        third
                            .lock()
                            .unwrap()
                            .recv_timeout(Duration::from_secs(5))
                            .unwrap();
                        Err(Error::Failed)
                    }
                    1 => Ok(i),
                    _ => wait_for_cancellation(&started),
                },
                |_| false,
            )
        });
        assert_eq!(result, Err(Error::Failed));
    }

    #[test]
    fn ordered_helpers_stop_starting_when_all_required_items_are_claimed() {
        for stop_at_first in [false, true] {
            let (started, wait) = mpsc::channel();
            let wait = Mutex::new(wait);
            let result = pool().install(|| {
                try_map_until_with_helpers(
                    vec![0, 1],
                    move || {
                        let _ = wait_for_cancellation(&started);
                        None::<Helper<()>>
                    },
                    move |_, i| {
                        if i == 0 {
                            wait.lock()
                                .unwrap()
                                .recv_timeout(Duration::from_secs(5))
                                .unwrap();
                        }
                        cancellation::check()?;
                        Ok::<_, Error>(i)
                    },
                    move |_| stop_at_first,
                )
            });
            assert_eq!(
                result.unwrap(),
                if stop_at_first { vec![0] } else { vec![0, 1] }
            );
        }
    }

    #[test]
    fn ordered_terminal_result_cancels_blocked_suffix() {
        for fail in [false, true] {
            let (started, wait) = mpsc::channel();
            let wait = Mutex::new(wait);
            let result = pool().install(|| {
                try_map_until(
                    (0..2).collect(),
                    move |i| {
                        if i == 1 {
                            wait_for_cancellation(&started)
                        } else {
                            wait.lock()
                                .unwrap()
                                .recv_timeout(Duration::from_secs(10))
                                .unwrap();
                            if fail {
                                Err(Error::Failed)
                            } else {
                                Ok(0)
                            }
                        }
                    },
                    |_| true,
                )
            });
            assert_eq!(
                result,
                if fail {
                    Err(Error::Failed)
                } else {
                    Ok(vec![0])
                }
            );
        }
    }

    #[test]
    fn ordered_work_preserves_all_required_results_and_errors() {
        pool().install(|| {
            assert_eq!(
                try_map_until((0..8).collect(), Ok::<_, Error>, |_| false),
                Ok((0..8).collect())
            );
            assert_eq!(
                try_map_until((0..0).collect(), Ok::<_, Error>, |_| false),
                Ok(vec![])
            );
            assert_eq!(
                try_map_until(
                    (0..2).collect(),
                    |i| {
                        if i == 0 {
                            Err(Error::Failed)
                        } else {
                            Ok(i)
                        }
                    },
                    |_| true
                ),
                Err(Error::Failed)
            );
        });
    }

    #[test]
    fn nested_terminal_result_is_not_trapped_behind_speculative_work() {
        fn tree(path: usize, depth: usize, seed: usize) -> Result<bool, Cancelled> {
            if depth == 0 {
                // The sequential first leaf always succeeds. Later leaves
                // may block forever unless an earlier prefix cancels them.
                if path != 16 && (path * 371 + seed * 17) % 5 < 2 {
                    while cancellation::check().is_ok() {
                        std::thread::sleep(Duration::from_millis(1));
                    }
                    cancellation::check()?;
                }
                std::thread::sleep(Duration::from_micros(
                    ((path * 97 + seed * 71) % 10 * 100) as u64,
                ));
                return Ok(true);
            }
            let prefix = try_map_until(
                (0..2).collect(),
                move |side| tree(path * 2 + side, depth - 1, seed),
                |solved| *solved,
            )?;
            assert_eq!(prefix, vec![true]);
            Ok(true)
        }

        let parent = CancellationToken::default();
        let token = parent.clone();
        let (done, wait) = mpsc::channel();
        let worker = std::thread::spawn(move || {
            let pool = rayon::ThreadPoolBuilder::new()
                .num_threads(3)
                .build()
                .unwrap();
            let result = pool.install(|| {
                let _guard = CancellationGuard::new(Some(token));
                for seed in 0..64 {
                    tree(1, 4, seed)?;
                    // Exercise an ordered search nested inside a fail-fast batch.
                    try_map((0..2).collect(), move |_| tree(1, 4, seed))?;
                }
                Ok::<_, Cancelled>(())
            });
            assert!(pool
                .broadcast(|_| CURRENT_GROUP.with(|group| group.borrow().is_none()))
                .into_iter()
                .all(|v| v));
            done.send(result).unwrap();
        });
        let result = wait.recv_timeout(Duration::from_secs(10));
        // Rescue a regression before failing so the test never leaves hung
        // Rayon workers or poisons subsequent tests.
        parent.cancel();
        worker.join().unwrap();
        assert_eq!(result, Ok(Ok(())));
    }

    #[test]
    fn request_cancel_reaches_running_nested_checkpoints_without_callbacks() {
        let parent = CancellationToken::default();
        let token = parent.clone();
        let (started, wait) = mpsc::channel();
        let worker = std::thread::spawn(move || {
            pool().install(|| {
                let _guard = CancellationGuard::new(Some(token));
                try_map((0..1).collect(), move |_| {
                    let started = started.clone();
                    try_map_until(
                        (0..1).collect(),
                        move |_| -> Result<usize, Error> {
                            started.send(()).unwrap();
                            let deadline = std::time::Instant::now() + Duration::from_secs(10);
                            loop {
                                cancellation::check().map_err(Error::from)?;
                                assert!(
                                    std::time::Instant::now() < deadline,
                                    "parent request was not observed"
                                );
                                std::thread::yield_now();
                            }
                        },
                        |_| false,
                    )
                })
            })
        });
        wait.recv_timeout(Duration::from_secs(10)).unwrap();
        parent.request_cancel();
        assert_eq!(worker.join().unwrap(), Err(Error::Cancelled));
    }

    #[test]
    fn panic_cancels_blocked_siblings_before_the_map_joins_them() {
        let pool = pool();
        // Both work closures and the ordered helper's stop predicate must
        // cancel blocked siblings before the map waits for them to finish.
        for mode in 0..3 {
            let (started, wait) = mpsc::channel();
            let wait = Mutex::new(wait);
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                pool.install(|| {
                    let work = move |i| {
                        if i == 0 {
                            wait_for_cancellation(&started)
                        } else {
                            wait.lock()
                                .unwrap()
                                .recv_timeout(Duration::from_secs(10))
                                .unwrap();
                            if mode < 2 {
                                panic!("task panicked");
                            }
                            Ok(i)
                        }
                    };
                    if mode == 0 {
                        try_map(vec![0, 1], work)
                    } else {
                        try_map_until(vec![0, 1], work, |_| panic!("stop predicate panicked"))
                    }
                })
            }));
            let panic = result.unwrap_err();
            assert_eq!(
                panic.downcast_ref::<&str>(),
                Some(&if mode < 2 {
                    "task panicked"
                } else {
                    "stop predicate panicked"
                })
            );
            assert!(pool
                .broadcast(|_| cancellation::current().is_none())
                .into_iter()
                .all(|v| v));
        }
    }
}
