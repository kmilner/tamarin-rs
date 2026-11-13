//! Request-scoped cancellation shared by solver workers and blocking I/O.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc, Condvar, Mutex,
};
use std::time::Duration;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Cancelled;

impl std::fmt::Display for Cancelled {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("request cancelled")
    }
}
impl std::error::Error for Cancelled {}

#[derive(Default)]
struct State {
    cancelled: AtomicBool,
    callbacks: Mutex<BTreeMap<u64, Box<dyn Fn() + Send>>>,
    next_id: std::sync::atomic::AtomicU64,
    callbacks_fired: AtomicBool,
}

#[derive(Clone, Default)]
pub struct CancellationToken(Arc<State>);

impl CancellationToken {
    /// Mark cancellation without running potentially blocking cleanup.
    /// Call `cancel` on a blocking worker to complete callback cleanup.
    pub fn request_cancel(&self) {
        self.0.cancelled.store(true, Ordering::Relaxed);
    }

    pub fn cancel(&self) {
        self.request_cancel();
        // Serialize callback execution with deregistration. Once a blocking
        // operation drops its registration, no late callback can kill a
        // subprocess that has since been handed to another request.
        let callbacks = self.0.callbacks.lock().unwrap();
        if !self.0.callbacks_fired.swap(true, Ordering::Relaxed) {
            for callback in callbacks.values() {
                callback();
            }
        }
    }

    pub fn is_cancelled(&self) -> bool {
        self.0.cancelled.load(Ordering::Relaxed)
    }
    pub fn check(&self) -> Result<(), Cancelled> {
        if self.is_cancelled() {
            Err(Cancelled)
        } else {
            Ok(())
        }
    }
    pub fn on_cancel(&self, callback: impl Fn() + Send + 'static) -> Registration {
        let mut callbacks = self.0.callbacks.lock().unwrap();
        let id = self.0.next_id.fetch_add(1, Ordering::Relaxed);
        if self.is_cancelled() {
            callback();
        } else {
            callbacks.insert(id, Box::new(callback));
        }
        Registration {
            token: self.clone(),
            id,
        }
    }
}

pub struct Registration {
    token: CancellationToken,
    id: u64,
}
impl Drop for Registration {
    fn drop(&mut self) {
        self.token.0.callbacks.lock().unwrap().remove(&self.id);
    }
}

thread_local! {
    static CURRENT: RefCell<Option<CancellationToken>> = const { RefCell::new(None) };
}

pub fn current() -> Option<CancellationToken> {
    CURRENT.with(|cell| cell.borrow().clone())
}
#[inline]
pub fn check() -> Result<(), Cancelled> {
    CURRENT.with(|cell| {
        cell.borrow()
            .as_ref()
            .map_or(Ok(()), CancellationToken::check)
    })
}

/// Must be installed explicitly on each Rayon/scoped worker, including when
/// the inherited token is None, and dropped on the thread that installed it.
#[must_use]
pub struct CancellationGuard {
    previous: Option<CancellationToken>,
    _not_send: std::marker::PhantomData<std::rc::Rc<()>>,
}
impl CancellationGuard {
    pub fn new(token: Option<CancellationToken>) -> Self {
        Self {
            previous: CURRENT.with(|cell| cell.replace(token)),
            _not_send: std::marker::PhantomData,
        }
    }
}
impl Drop for CancellationGuard {
    fn drop(&mut self) {
        CURRENT.with(|cell| cell.replace(self.previous.take()));
    }
}

/// A cancelled waiter must not kill the request which owns the mutex.
#[inline]
pub fn lock<T>(mutex: &parking_lot::Mutex<T>) -> Result<parking_lot::MutexGuard<'_, T>, Cancelled> {
    // Cached Maude operations frequently take an uncontended lock. Keep this
    // path free of token refcount changes and timed-wait setup.
    if let Some(guard) = mutex.try_lock() {
        check()?;
        return Ok(guard);
    }
    lock_contended(mutex)
}

#[cold]
fn lock_contended<T>(
    mutex: &parking_lot::Mutex<T>,
) -> Result<parking_lot::MutexGuard<'_, T>, Cancelled> {
    let Some(token) = current() else {
        return Ok(mutex.lock());
    };
    loop {
        token.check()?;
        // Wake on unlock, just like an ordinary mutex. The timeout only
        // bounds cancellation latency when an unrelated owner stays busy.
        if let Some(guard) = mutex.try_lock_for(Duration::from_secs(1)) {
            token.check()?;
            return Ok(guard);
        }
    }
}

enum CellState<T, E> {
    Empty,
    Building,
    Ready(Result<T, E>),
}

/// Single-flight initialization. Cancellation/panics leave the slot empty;
/// other waiters retry using their own request rather than inheriting its error.
/// Completed values and ordinary errors retain the original OnceLock policy.
pub struct CancellableOnce<T, E> {
    state: Mutex<CellState<T, E>>,
    ready: Condvar,
}
impl<T, E> Default for CancellableOnce<T, E> {
    fn default() -> Self {
        Self {
            state: Mutex::new(CellState::Empty),
            ready: Condvar::new(),
        }
    }
}
impl<T: Clone, E: Clone + From<Cancelled>> CancellableOnce<T, E> {
    pub fn from_result(value: Result<T, E>) -> Self {
        Self {
            state: Mutex::new(CellState::Ready(value)),
            ready: Condvar::new(),
        }
    }

    pub fn get(&self) -> Option<Result<T, E>> {
        match &*self.state.lock().unwrap() {
            CellState::Ready(value) => Some(value.clone()),
            _ => None,
        }
    }
    pub fn get_or_init(&self, build: impl FnOnce() -> Result<T, E>) -> Result<T, E> {
        let mut state = self.state.lock().unwrap();
        loop {
            check()?;
            match &*state {
                CellState::Ready(value) => return value.clone(),
                CellState::Building => {
                    state = if current().is_some() {
                        self.ready
                            .wait_timeout(state, Duration::from_millis(250))
                            .unwrap()
                            .0
                    } else {
                        self.ready.wait(state).unwrap()
                    }
                }
                CellState::Empty => {
                    *state = CellState::Building;
                    break;
                }
            }
        }
        drop(state);
        struct Reset<'a, T, E>(&'a CancellableOnce<T, E>);
        impl<T, E> Drop for Reset<'_, T, E> {
            fn drop(&mut self) {
                let mut state = self.0.state.lock().unwrap();
                if matches!(*state, CellState::Building) {
                    *state = CellState::Empty;
                }
                self.0.ready.notify_all();
            }
        }
        let _reset = Reset(self);
        let value = build();
        check()?;
        *self.state.lock().unwrap() = CellState::Ready(value.clone());
        value
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::mpsc;

    #[test]
    fn cancelled_initializer_is_not_cached_and_waiter_retries() {
        let cell = Arc::new(CancellableOnce::<usize, Cancelled>::default());
        let token = CancellationToken::default();
        let (started_tx, started_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let owner_cell = cell.clone();
        let owner_token = token.clone();
        let owner = std::thread::spawn(move || {
            let _guard = CancellationGuard::new(Some(owner_token));
            owner_cell.get_or_init(|| {
                started_tx.send(()).unwrap();
                release_rx.recv().unwrap();
                // Even a superficially successful partial result cannot escape.
                Ok(13)
            })
        });
        started_rx.recv_timeout(Duration::from_secs(5)).unwrap();
        let waiter_cell = cell.clone();
        let waiter = std::thread::spawn(move || waiter_cell.get_or_init(|| Ok(42)));
        token.cancel();
        release_tx.send(()).unwrap();
        assert_eq!(owner.join().unwrap(), Err(Cancelled));
        assert_eq!(waiter.join().unwrap(), Ok(42));
        assert_eq!(cell.get(), Some(Ok(42)));
    }

    #[test]
    fn cancelled_waiter_leaves_initializer_alone() {
        let cell = Arc::new(CancellableOnce::<usize, Cancelled>::default());
        let (started_tx, started_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let owner_cell = cell.clone();
        let owner = std::thread::spawn(move || {
            owner_cell.get_or_init(|| {
                started_tx.send(()).unwrap();
                release_rx.recv().unwrap();
                Ok(42)
            })
        });
        started_rx.recv_timeout(Duration::from_secs(5)).unwrap();
        let token = CancellationToken::default();
        let waiter_token = token.clone();
        let waiter_cell = cell.clone();
        let (done_tx, done_rx) = mpsc::channel();
        let waiter = std::thread::spawn(move || {
            let _guard = CancellationGuard::new(Some(waiter_token));
            done_tx
                .send(waiter_cell.get_or_init(|| panic!("waiter became initializer")))
                .unwrap();
        });
        token.cancel();
        assert_eq!(
            done_rx.recv_timeout(Duration::from_secs(5)).unwrap(),
            Err(Cancelled)
        );
        release_tx.send(()).unwrap();
        waiter.join().unwrap();
        assert_eq!(owner.join().unwrap(), Ok(42));
        assert_eq!(cell.get(), Some(Ok(42)));
    }

    #[test]
    fn deregistered_callback_cannot_affect_later_work() {
        let token = CancellationToken::default();
        let called = Arc::new(AtomicBool::new(false));
        let flag = called.clone();
        let registration = token.on_cancel(move || {
            flag.store(true, Ordering::Relaxed);
        });
        drop(registration);
        token.cancel();
        assert!(!called.load(Ordering::Relaxed));
        let flag = called.clone();
        let _registration = token.on_cancel(move || {
            flag.store(true, Ordering::Relaxed);
        });
        assert!(called.load(Ordering::Relaxed));
    }
}
