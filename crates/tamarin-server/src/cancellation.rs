// Currently GPL 3.0; see README.md for licensing details.

//! Cancellation for blocking proof requests, keyed by the URL the UI sends.

use std::collections::BTreeMap;
use std::sync::Arc;
use tamarin_utils::cancellation::{CancellationToken, Cancelled};

use parking_lot::Mutex;

#[derive(Default)]
pub struct ProofRequests {
    active: Mutex<BTreeMap<String, Vec<Arc<RequestState>>>>,
    cancel_cleanup: Option<fn()>,
}

impl ProofRequests {
    pub fn new(cancel_cleanup: Option<fn()>) -> Self {
        Self {
            cancel_cleanup,
            ..Self::default()
        }
    }

    pub(crate) fn register(&self, path: String) -> ProofRequest<'_> {
        let state = Arc::new(RequestState {
            cancelled: CancellationToken::default(),
            phase: tokio::sync::watch::channel(WorkerPhase::Queued).0,
        });
        self.active
            .lock()
            .entry(path.clone())
            .or_default()
            .push(state.clone());
        ProofRequest {
            registry: self,
            path,
            state,
            registered: true,
            submitted: false,
        }
    }

    fn signal(&self, path: &str) -> Vec<Arc<RequestState>> {
        // Serialize cancellation with finish(), so a request cannot be
        // acknowledged as cancelled and then publish a successful result.
        let active = self.active.lock();
        let requests = active.get(path).cloned().unwrap_or_default();
        for request in &requests {
            request.request_cancel();
        }
        requests
    }

    pub(crate) async fn cancel(&self, path: &str) {
        let requests = self.signal(path);
        if requests.is_empty() {
            return;
        }
        cancel_in_background(requests.clone())
            .await
            .expect("cancellation cleanup panicked");
        for request in requests {
            request.wait_done().await;
        }
        // One best-effort collection after callbacks and proof workers finish.
        // Keep it off both the async executor and the possibly saturated pool.
        if let Some(cleanup) = self.cancel_cleanup {
            let (done, receiver) = tokio::sync::oneshot::channel();
            std::thread::spawn(move || {
                cleanup();
                let _ = done.send(());
            });
            receiver.await.expect("allocator cleanup panicked");
        }
    }
}

/// Cleanup must have execution capacity independent of Tokio's blocking
/// pool: that pool may be full of proof workers waiting for these callbacks
/// to interrupt their subprocess reads. Dropping the receiver does not stop
/// cleanup (for example when the HTTP request itself is abandoned).
fn cancel_in_background(requests: Vec<Arc<RequestState>>) -> tokio::sync::oneshot::Receiver<()> {
    let (done, receiver) = tokio::sync::oneshot::channel();
    std::thread::spawn(move || {
        for request in requests {
            request.cancelled.cancel();
        }
        let _ = done.send(());
    });
    receiver
}

#[derive(PartialEq, Eq)]
enum WorkerPhase {
    Queued,
    Running,
    Finished,
}

struct RequestState {
    cancelled: CancellationToken,
    phase: tokio::sync::watch::Sender<WorkerPhase>,
}

impl RequestState {
    fn request_cancel(&self) {
        // Serialize admission with cancellation: either the worker starts
        // and must be cleaned up, or it is disarmed before doing any work.
        self.phase.send_if_modified(|phase| {
            self.cancelled.request_cancel();
            if *phase == WorkerPhase::Queued {
                *phase = WorkerPhase::Finished;
                true
            } else {
                false
            }
        });
    }

    async fn wait_done(&self) {
        let mut phase = self.phase.subscribe();
        while *phase.borrow_and_update() != WorkerPhase::Finished {
            if phase.changed().await.is_err() {
                break;
            }
        }
    }
}

/// Owned by the blocking closure. Once admitted, its drop signals actual
/// cleanup even if the HTTP future has already been dropped.
struct ProofWorker(Arc<RequestState>);
impl ProofWorker {
    fn enter(&self) -> Result<tamarin_utils::cancellation::CancellationGuard, Cancelled> {
        let admitted = self.0.phase.send_if_modified(|phase| {
            if *phase == WorkerPhase::Queued {
                *phase = WorkerPhase::Running;
                true
            } else {
                false
            }
        });
        if !admitted {
            return Err(Cancelled);
        }
        Ok(tamarin_utils::cancellation::CancellationGuard::new(Some(
            self.0.cancelled.clone(),
        )))
    }
}
impl Drop for ProofWorker {
    fn drop(&mut self) {
        self.0.phase.send_replace(WorkerPhase::Finished);
    }
}

pub(crate) struct ProofRequest<'a> {
    registry: &'a ProofRequests,
    path: String,
    state: Arc<RequestState>,
    registered: bool,
    submitted: bool,
}

impl ProofRequest<'_> {
    /// Execute one blocking job per registration. Queued cancellation may
    /// return before Tokio dequeues the wrapper, which then rejects admission
    /// without invoking `work`. Running cancellation still waits for cleanup.
    pub(crate) async fn run<T, E>(
        &mut self,
        work: impl FnOnce() -> Result<T, E> + Send + 'static,
    ) -> Result<Result<T, E>, tokio::task::JoinError>
    where
        T: Send + 'static,
        E: From<Cancelled> + Send + 'static,
    {
        assert!(
            !std::mem::replace(&mut self.submitted, true),
            "one job per proof request"
        );
        let worker = ProofWorker(self.state.clone());
        let task = tokio::task::spawn_blocking(move || {
            let _guard = worker.enter().map_err(E::from)?;
            tamarin_utils::cancellation::check().map_err(E::from)?;
            let result = work();
            if worker.0.cancelled.is_cancelled() {
                // Release a completed result when cancellation wins this race.
                drop(result);
                return Err(E::from(Cancelled));
            }
            result
        });
        self.state.wait_done().await;
        if self.state.cancelled.is_cancelled() {
            return Ok(Err(E::from(Cancelled)));
        }
        task.await
    }

    #[cfg(test)]
    fn worker(&self) -> ProofWorker {
        ProofWorker(self.state.clone())
    }

    /// Finish under the same lock as cancellation, before publishing a result.
    pub(crate) fn finish(mut self) -> bool {
        let publish = self.remove();
        self.registered = false;
        publish
    }

    fn remove(&self) -> bool {
        let mut active = self.registry.active.lock();
        if let Some(requests) = active.get_mut(&self.path) {
            requests.retain(|flag| !Arc::ptr_eq(flag, &self.state));
            if requests.is_empty() {
                active.remove(&self.path);
            }
        }
        !self.state.cancelled.is_cancelled()
    }
}

impl Drop for ProofRequest<'_> {
    fn drop(&mut self) {
        // Dropping an HTTP future must also stop its detached blocking worker.
        if !self.registered {
            return;
        }
        self.state.request_cancel();
        self.remove();
        drop(cancel_in_background(vec![self.state.clone()]));
    }
}

/// Wait for shared proof state without trapping a cancelled request behind
/// a reader that is still replaying a stored proof.
pub(crate) fn lock<T>(mutex: &Mutex<T>) -> Result<parking_lot::MutexGuard<'_, T>, String> {
    tamarin_utils::cancellation::lock(mutex).map_err(|e| e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn allocator_cleanup_follows_callbacks_and_cancelled_result_drop() {
        use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
        static DROPPED: AtomicBool = AtomicBool::new(false);
        static CALLBACK_FINISHED: AtomicBool = AtomicBool::new(false);
        static CLEANED: AtomicUsize = AtomicUsize::new(0);
        struct ResultData;
        impl Drop for ResultData {
            fn drop(&mut self) {
                DROPPED.store(true, Ordering::SeqCst);
            }
        }
        let requests = ProofRequests::new(Some(|| {
            assert!(DROPPED.load(Ordering::SeqCst));
            assert!(CALLBACK_FINISHED.load(Ordering::SeqCst));
            CLEANED.fetch_add(1, Ordering::SeqCst);
        }));
        let mut successful = requests.register("/proof".into());
        assert_eq!(
            successful.run(|| Ok::<_, Cancelled>(42)).await.unwrap(),
            Ok(42)
        );
        assert!(successful.finish());
        requests.cancel("/missing").await;
        assert_eq!(CLEANED.load(Ordering::SeqCst), 0);

        let (entered_tx, entered_rx) = tokio::sync::oneshot::channel();
        let proof = async {
            let mut cancelled = requests.register("/proof".into());
            let result = cancelled
                .run(move || {
                    let (release_tx, release_rx) = std::sync::mpsc::channel();
                    let token = tamarin_utils::cancellation::current().unwrap();
                    let _registration = token.on_cancel(move || {
                        release_tx.send(()).unwrap();
                        CALLBACK_FINISHED.store(true, Ordering::SeqCst);
                    });
                    entered_tx.send(()).unwrap();
                    release_rx
                        .recv_timeout(std::time::Duration::from_secs(5))
                        .unwrap();
                    // Even a completed result must be discarded on cancellation.
                    Ok::<_, Cancelled>(ResultData)
                })
                .await
                .unwrap();
            assert!(matches!(result, Err(Cancelled)));
            assert!(!cancelled.finish());
        };
        let stop = async {
            entered_rx.await.unwrap();
            requests.cancel("/proof").await;
        };
        tokio::join!(proof, stop);
        assert_eq!(CLEANED.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn cancellation_is_scoped_and_completed_requests_are_removed() {
        let requests = ProofRequests::default();
        let first = requests.register("/proof/one".into());
        let duplicate = requests.register("/proof/one".into());
        let other = requests.register("/proof/two".into());
        requests.signal("/proof/one");
        assert!(!first.finish());
        assert!(!duplicate.finish());
        assert!(other.finish());
        assert!(requests.active.lock().is_empty());
        assert!(requests.register("/proof/one".into()).finish());
    }

    #[tokio::test]
    async fn acknowledgement_waits_for_worker_and_old_cleanup_preserves_restart() {
        let requests = ProofRequests::default();
        let old = requests.register("/proof".into());
        let worker = old.worker();
        drop(worker.enter().unwrap());
        assert!(tokio::time::timeout(
            std::time::Duration::from_millis(20),
            requests.cancel("/proof")
        )
        .await
        .is_err());
        assert!(old.state.cancelled.is_cancelled());
        // A replacement can register while the old worker is unwinding.
        let new = requests.register("/proof".into());
        drop(worker);
        assert!(!old.finish());
        assert_eq!(requests.active.lock()["/proof"].len(), 1);
        assert!(new.finish());
    }

    #[tokio::test]
    async fn blocking_cleanup_releases_registry_and_async_executor() {
        let requests = Arc::new(ProofRequests::default());
        let request = requests.register("/proof".into());
        let worker = request.worker();
        let (entered_tx, entered_rx) = tokio::sync::oneshot::channel();
        let entered_tx = std::sync::Mutex::new(Some(entered_tx));
        let (release_tx, release_rx) = std::sync::mpsc::channel();
        let release_rx = std::sync::Mutex::new(release_rx);
        let _registration = request.state.cancelled.on_cancel(move || {
            entered_tx.lock().unwrap().take().unwrap().send(()).unwrap();
            release_rx
                .lock()
                .unwrap()
                .recv_timeout(std::time::Duration::from_secs(5))
                .unwrap();
        });
        let cancelling = requests.clone();
        let cancel = tokio::spawn(async move { cancelling.cancel("/proof").await });
        tokio::time::timeout(std::time::Duration::from_secs(2), entered_rx)
            .await
            .unwrap()
            .unwrap();
        // This runs on the same single-thread Tokio executor while the
        // callback is still blocked, and needs the registry mutex.
        let replacement = requests.register("/proof".into());
        assert!(
            !request.finish(),
            "marked cancellation must prevent publication"
        );
        let replacement_token = replacement.state.cancelled.clone();
        assert!(replacement.finish());
        assert!(
            !replacement_token.is_cancelled(),
            "successful finish is disarmed"
        );
        release_tx.send(()).unwrap();
        drop(worker);
        cancel.await.unwrap();
    }

    #[test]
    fn explicit_cancellation_works_with_a_full_blocking_pool() {
        check_cleanup_with_full_blocking_pool(false);
    }

    #[test]
    fn dropped_request_cleanup_works_with_a_full_blocking_pool() {
        check_cleanup_with_full_blocking_pool(true);
    }

    fn check_cleanup_with_full_blocking_pool(drop_request: bool) {
        use std::time::Duration;
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_time()
            .max_blocking_threads(1)
            .build()
            .unwrap();
        runtime.block_on(async {
            let requests = ProofRequests::default();
            let mut request = Some(requests.register("/proof".into()));
            let worker = request.as_ref().unwrap().worker();
            let (entered_tx, entered_rx) = tokio::sync::oneshot::channel();
            let (release_tx, release_rx) = std::sync::mpsc::channel();
            let emergency_release = release_tx.clone();
            let mut task = tokio::task::spawn_blocking(move || {
                let _guard = worker.enter().unwrap();
                let _registration =
                    tamarin_utils::cancellation::current()
                        .unwrap()
                        .on_cancel(move || {
                            let _ = release_tx.send(());
                        });
                entered_tx.send(()).unwrap();
                // Models a subprocess read: the flag alone cannot unblock
                // this worker; its cancellation callback must execute.
                release_rx.recv_timeout(Duration::from_secs(10)).unwrap();
            });
            entered_rx.await.unwrap();
            let stopped = tokio::time::timeout(Duration::from_secs(2), async {
                if drop_request {
                    drop(request.take());
                } else {
                    requests.cancel("/proof").await;
                }
                (&mut task).await.unwrap();
            })
            .await;
            // A regression must fail promptly rather than deadlocking the
            // runtime's shutdown while its only blocking thread is occupied.
            if stopped.is_err() {
                let _ = emergency_release.send(());
                task.await.unwrap();
            }
            assert!(
                stopped.is_ok(),
                "cleanup starved behind its own proof worker"
            );
            if let Some(request) = request {
                assert!(!request.finish());
            }
            assert!(requests.active.lock().is_empty());
            assert!(requests.register("/proof".into()).finish());
        });
    }

    #[test]
    fn queued_cancellation_returns_before_unrelated_work_finishes() {
        check_queued_cancellation(false);
    }

    #[test]
    fn dropping_a_queued_request_prevents_it_from_running() {
        check_queued_cancellation(true);
    }

    fn check_queued_cancellation(drop_request: bool) {
        use std::sync::atomic::{AtomicBool, Ordering};
        use std::time::Duration;
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_time()
            .max_blocking_threads(1)
            .build()
            .unwrap();
        runtime.block_on(async {
            let (release_tx, release_rx) = std::sync::mpsc::channel();
            let (entered_tx, entered_rx) = tokio::sync::oneshot::channel();
            let unrelated = tokio::task::spawn_blocking(move || {
                entered_tx.send(()).unwrap();
                // Dropping the sender also releases this task on test failure.
                let _ = release_rx.recv();
            });
            entered_rx.await.unwrap();
            let requests = ProofRequests::new(Some(|| {}));
            let mut request = requests.register("/proof".into());
            let old_state = request.state.clone();
            let ran = Arc::new(AtomicBool::new(false));
            let job_ran = ran.clone();
            let mut response = Box::pin(request.run(move || {
                job_ran.store(true, Ordering::Relaxed);
                Ok::<_, Cancelled>(())
            }));
            // Poll submission while the sole blocking worker is occupied.
            assert!(
                tokio::time::timeout(Duration::from_millis(20), response.as_mut())
                    .await
                    .is_err()
            );
            if drop_request {
                drop(response);
                drop(request);
            } else {
                tokio::time::timeout(Duration::from_secs(2), requests.cancel("/proof"))
                    .await
                    .expect("queued cancellation must acknowledge promptly");
                let result = tokio::time::timeout(Duration::from_secs(2), response.as_mut())
                    .await
                    .expect("the original HTTP handler must also complete")
                    .unwrap();
                assert_eq!(result, Err(Cancelled));
                drop(response);
                assert!(!request.finish());
            }
            tokio::time::timeout(Duration::from_secs(2), old_state.wait_done())
                .await
                .unwrap();
            assert!(!unrelated.is_finished(), "unrelated work remains untouched");
            let mut replacement = requests.register("/proof".into());
            release_tx.send(()).unwrap();
            unrelated.await.unwrap();
            // The old wrapper is now dequeued too. It must not execute the
            // cancelled job or interfere with a new request for the same URL.
            assert_eq!(
                replacement.run(|| Ok::<_, Cancelled>(42)).await.unwrap(),
                Ok(42)
            );
            assert!(replacement.finish());
            assert!(!ran.load(Ordering::Relaxed));
            assert!(requests.active.lock().is_empty());
        });
    }

    #[test]
    fn dropping_a_request_cancels_its_worker() {
        let requests = ProofRequests::default();
        let request = requests.register("/proof".into());
        let flag = request.state.cancelled.clone();
        drop(request);
        assert!(flag.is_cancelled());
        assert!(requests.active.lock().is_empty());
    }
}
