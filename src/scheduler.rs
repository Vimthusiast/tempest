use std::collections::{HashMap, HashSet, VecDeque};

use tokio::sync::{mpsc, oneshot};

use crate::core::TempestStr;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum AccessMode {
    IntentShared,
    IntentExclusive,
    Shared,
    Exclusive,
}

/// ## Resource Hierarchy
///
/// - `Catalog`
///   - `Database(db_name)`
///     - `Table(db_name, table_name)`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Resource {
    Catalog,
    Database(TempestStr<'static>),
    Table(TempestStr<'static>, TempestStr<'static>),
}

/// # Lock State
///
/// ## S (Shared)
///
/// This object is locked for reading.
/// Allows other `S`/`IS` locks, but blocks `X`/`IX`.
///
/// ## X (Exclusive)
///
/// This object is locked for writing/deletion.
/// Blocks all `S`/`IS`/`IX` locks.
///
/// ## IS (Intent Shared)
///
/// An object further down the hierarchy is locked for reading.
/// Blocks `X` locks on the parent.
///
/// ## IX (Intent Exclusive)
///
/// An object further down the hierarchy is locked for writing/deletion.
/// Blocks `S`/`X` locks on the parent.
///
/// # Compatability Between Lock States
///
/// | Requested \ Held | IS  | IX  |  S  | X  |
/// |------------------|-----|-----|-----|----|
/// |        IS        | Yes | Yes | Yes | No |
/// |        IX        | Yes | Yes | No  | No |
/// |        S         | Yes | No  | Yes | No |
/// |        X         | No  | No  | No  | No |
#[derive(Default)]
struct LockState {
    is_locks: u32,
    ix_locks: u32,
    s_locks: u32,
    x_locked: bool,
}

impl LockState {
    #[inline]
    const fn allows(&self, access_mode: &AccessMode) -> bool {
        match access_mode {
            AccessMode::IntentShared => !self.x_locked,
            AccessMode::IntentExclusive => self.s_locks == 0 && !self.x_locked,
            AccessMode::Shared => self.ix_locks == 0 && !self.x_locked,
            AccessMode::Exclusive => {
                self.is_locks == 0 && self.ix_locks == 0 && self.s_locks == 0 && !self.x_locked
            }
        }
    }

    fn acquire(&mut self, access_mode: &AccessMode) {
        match access_mode {
            AccessMode::IntentShared => self.is_locks += 1,
            AccessMode::IntentExclusive => self.ix_locks += 1,
            AccessMode::Shared => self.s_locks += 1,
            AccessMode::Exclusive => self.x_locked = true,
        }
    }

    fn release(&mut self, access_mode: &AccessMode) {
        match access_mode {
            AccessMode::IntentShared => self.is_locks -= 1,
            AccessMode::IntentExclusive => self.ix_locks -= 1,
            AccessMode::Shared => self.s_locks -= 1,
            AccessMode::Exclusive => self.x_locked = false,
        }
    }
}

pub(crate) type ResourceAccessSet = HashSet<(Resource, AccessMode)>;

pub(crate) struct PendingRequest {
    resources: ResourceAccessSet,
    grant_tx: oneshot::Sender<AccessGuard>,
}

pub(crate) enum DispatcherMessage {
    Acquire(PendingRequest),
    Release(ResourceAccessSet),
}

#[derive(Debug)]
pub(crate) struct AccessGuard {
    resources: ResourceAccessSet,
    tx_to_dispatcher: mpsc::UnboundedSender<DispatcherMessage>,
}

impl Drop for AccessGuard {
    fn drop(&mut self) {
        // signal to the dispatcher that the resources can be accessed again
        let _ = self
            .tx_to_dispatcher
            // PERF: We could take out the Set, instead of cloning it,
            // since the value will have been dropped after this function returns
            .send(DispatcherMessage::Release(self.resources.clone()));
    }
}

struct QueuedRequest {
    request: PendingRequest,
    skip_count: u32,
}

impl From<PendingRequest> for QueuedRequest {
    fn from(request: PendingRequest) -> Self {
        Self {
            request,
            skip_count: 0,
        }
    }
}

struct AccessDispatcher {
    resource_accesses: HashMap<Resource, LockState>,
    acquire_queue: VecDeque<QueuedRequest>,
    /// The transmitter of messages to this dispatcher.
    tx: mpsc::UnboundedSender<DispatcherMessage>,
    /// The receiver of messages to this dispatcher.
    rx: mpsc::UnboundedReceiver<DispatcherMessage>,
    /// The maximum amount of times a
    max_skip_tolerance: u32,
}

impl AccessDispatcher {
    async fn run(&mut self) {
        loop {
            tokio::select! {
                Some(msg) = self.rx.recv() => self.handle_message(msg).await,
                else => break,
            }
        }
    }

    async fn handle_message(&mut self, message: DispatcherMessage) {
        match message {
            DispatcherMessage::Acquire(request) => self.handle_acquire_message(request).await,
            DispatcherMessage::Release(resources) => self.handle_release_message(resources).await,
        }
    }

    async fn handle_acquire_message(&mut self, request: PendingRequest) {
        let mut all_allowed = true;
        for (resource, access_mode) in request.resources.iter() {
            if let Some(ls) = self.resource_accesses.get(resource)
                && !ls.allows(access_mode)
            {
                all_allowed = false;
                break;
            }
        }
        if !all_allowed {
            self.acquire_queue.push_back(request.into());
        } else {
            for (resource, access_mode) in request.resources.clone() {
                match self.resource_accesses.entry(resource) {
                    std::collections::hash_map::Entry::Occupied(mut e) => {
                        e.get_mut().acquire(&access_mode);
                    }
                    std::collections::hash_map::Entry::Vacant(e) => {
                        let lock_state = e.insert(LockState::default());
                        lock_state.acquire(&access_mode);
                    }
                }
            }
            let guard = AccessGuard {
                resources: request.resources,
                tx_to_dispatcher: self.tx.clone(),
            };
            request
                .grant_tx
                .send(guard)
                .expect("should not have been granted access yet");
        }
    }

    async fn handle_release_message(&mut self, resources: ResourceAccessSet) {
        for (resource, access_mode) in resources {
            let lock_state = self
                .resource_accesses
                .get_mut(&resource)
                .expect("resource should have been locked before");
            lock_state.release(&access_mode);
        }
    }
}

pub(crate) struct AccessManager {
    tx_to_dispatcher: mpsc::UnboundedSender<DispatcherMessage>,
}

impl AccessManager {
    pub(crate) async fn init() -> Self {
        let (tx_to_dispatcher, rx_to_dispatcher) = mpsc::unbounded_channel();

        // maximum amounts of skips before prioritizing an access request
        let max_skip_tolerance = 64;

        let tx_to_dispatcher_clone = tx_to_dispatcher.clone();
        let mut access_dispatcher = AccessDispatcher {
            resource_accesses: HashMap::new(),
            acquire_queue: VecDeque::new(),
            rx: rx_to_dispatcher,
            tx: tx_to_dispatcher_clone,
            max_skip_tolerance,
        };
        let _dispatcher_handle = tokio::task::spawn(async move {
            access_dispatcher.run().await;
        });

        Self { tx_to_dispatcher }
    }

    pub(crate) async fn acquire(&self, resources: ResourceAccessSet) -> AccessGuard {
        let (tx, rx) = oneshot::channel();

        let mut expanded_set = resources;
        let mut parents = Vec::new();
        for (res, mode) in &expanded_set {
            let parent_mode = match mode {
                AccessMode::Shared | AccessMode::IntentShared => AccessMode::IntentShared,
                AccessMode::Exclusive | AccessMode::IntentExclusive => AccessMode::IntentExclusive,
            };
            match res {
                Resource::Catalog => {} // root of the tree
                Resource::Database(_) => {
                    parents.push((Resource::Catalog, parent_mode));
                }
                Resource::Table(db, _) => {
                    parents.push((Resource::Database(db.clone()), parent_mode.clone()));
                    parents.push((Resource::Catalog, parent_mode));
                }
            }
        }
        expanded_set.extend(parents);

        let request = PendingRequest {
            resources: expanded_set,
            grant_tx: tx,
        };

        self.tx_to_dispatcher
            .send(DispatcherMessage::Acquire(request))
            .expect("Dispatcher channel should not be closed");

        rx.await.expect("Dispatcher task dropped")
    }
}
