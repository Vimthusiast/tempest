use std::collections::{HashMap, HashSet, VecDeque};

use tokio::sync::{mpsc, oneshot};

use crate::core::TempestStr;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum AccessMode {
    Exclusive,
    Shared,
    IntentExclusive,
    IntentShared,
}

impl AccessMode {
    /// Limit this `AccessMode` by `target`. `IS` is the lowest mode.
    ///
    /// **Rules:**
    ///
    /// - `X -> target`: Anything is `<= X`.
    /// - `S -> IS`: `S` can go to `IS` but never `IX`.
    /// - `IX -> IS`: `IX` can to `IS`.
    /// - `old -> old`: All others will stay.
    ///
    /// This means that any old mode that gets downgraded with target `IS`, always becomes `IS` and
    /// that `X` can be downgraded to any new target mode, allowing for many downgrade operations.
    #[inline]
    const fn downgrade(&self, target: Self) -> Self {
        match (self, target) {
            (AccessMode::Exclusive, limit) => limit,
            (AccessMode::Shared, AccessMode::IntentShared) => AccessMode::IntentShared,
            (AccessMode::IntentExclusive, AccessMode::IntentShared) => AccessMode::IntentShared,
            (current, _) => *current,
        }
    }
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
/// ## X (Exclusive)
///
/// This object is locked for writing/deletion.
/// Blocks all `S`/`IS`/`IX` locks.
///
/// ## S (Shared)
///
/// This object is locked for reading.
/// Allows other `S`/`IS` locks, but blocks `X`/`IX`.
///
/// ## IX (Intent Exclusive)
///
/// An object further down the hierarchy is locked for writing/deletion.
/// Blocks `S`/`X` locks on the parent.
///
/// ## IS (Intent Shared)
///
/// An object further down the hierarchy is locked for reading.
/// Blocks `X` locks on the parent.
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
    x_locked: bool,
    s_locks: u32,
    ix_locks: u32,
    is_locks: u32,
}

impl LockState {
    #[inline]
    const fn allows(&self, access_mode: &AccessMode) -> bool {
        match access_mode {
            AccessMode::Exclusive => {
                self.is_locks == 0 && self.ix_locks == 0 && self.s_locks == 0 && !self.x_locked
            }
            AccessMode::Shared => self.ix_locks == 0 && !self.x_locked,
            AccessMode::IntentExclusive => self.s_locks == 0 && !self.x_locked,
            AccessMode::IntentShared => !self.x_locked,
        }
    }

    fn acquire(&mut self, access_mode: &AccessMode) {
        match access_mode {
            AccessMode::Exclusive => self.x_locked = true,
            AccessMode::Shared => self.s_locks += 1,
            AccessMode::IntentExclusive => self.ix_locks += 1,
            AccessMode::IntentShared => self.is_locks += 1,
        }
    }

    fn release(&mut self, access_mode: &AccessMode) {
        match access_mode {
            AccessMode::Exclusive => self.x_locked = false,
            AccessMode::Shared => self.s_locks -= 1,
            AccessMode::IntentExclusive => self.ix_locks -= 1,
            AccessMode::IntentShared => self.is_locks -= 1,
        }
    }

    /// Returns `true` when all the locks are released, otherwise returns `false`.
    #[inline]
    const fn all_released(&self) -> bool {
        self.is_locks == 0 && self.ix_locks == 0 && self.s_locks == 0 && !self.x_locked
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
    /// Downgrades to a set with lower access modes.
    /// This set is created through the use of [`AccessMode::downgrade`].
    Downgrade {
        old: ResourceAccessSet,
        new: ResourceAccessSet,
    },
}

#[derive(Debug)]
pub(crate) struct AccessGuard {
    resources: Option<ResourceAccessSet>,
    tx_to_dispatcher: mpsc::UnboundedSender<DispatcherMessage>,
}

impl AccessGuard {
    pub(crate) fn downgrade(&mut self, target: AccessMode) {
        let old = self
            .resources
            .take()
            .expect("Access guard must not have been released yet when downgrading");
        let new: ResourceAccessSet = old
            .iter()
            .map(|(res, mode)| (res.clone(), mode.downgrade(target)))
            .collect();
        self.resources = Some(new.clone());

        // WARN: we ignore the error here, cause if send fails, the program
        // is already in a bad state and expected to come to a crash?
        let _ = self
            .tx_to_dispatcher
            .send(DispatcherMessage::Downgrade { old, new });
    }
}

impl Drop for AccessGuard {
    fn drop(&mut self) {
        // signal to the dispatcher that the resources can be accessed again
        if let Some(resources) = self.resources.take() {
            // WARN: we ignore the error here, cause if send fails, the program
            // is already in a bad state and expected to come to a crash?
            let _ = self
                .tx_to_dispatcher
                .send(DispatcherMessage::Release(resources));
        }
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

// PERF: Instead of sending the whole `ResourceAccessSet` every time, we should give every
// `AccessGuard` a unique `usize` ID that we map to their respective access set.
struct AccessDispatcher {
    resource_accesses: HashMap<Resource, LockState>,
    acquire_queue: VecDeque<QueuedRequest>,
    /// The transmitter of messages to this dispatcher.
    tx: mpsc::UnboundedSender<DispatcherMessage>,
    /// The receiver of messages to this dispatcher.
    rx: mpsc::UnboundedReceiver<DispatcherMessage>,
    /// The maximum amount of times a [`QueuedRequest`] may be skipped over.
    max_skip_tolerance: u32,
}

impl AccessDispatcher {
    async fn run(&mut self) {
        loop {
            tokio::select! {
                Some(msg) = self.rx.recv() => self.handle_message(msg),
                else => break,
            }
        }
    }

    fn handle_message(&mut self, message: DispatcherMessage) {
        match message {
            DispatcherMessage::Acquire(request) => {
                self.acquire_queue.push_back(request.into());
                self.try_grant_waiting();
            }
            DispatcherMessage::Release(resources) => {
                self.release(&resources);
                self.try_grant_waiting();
            }
            // TODO: verify that `old` is actually a valid lock set and `new` is a subset of `old`
            // => This should be guranteed already, as we control the whole message passing infra,
            // but for safety, we should maybe put in some debug_assert! statements
            DispatcherMessage::Downgrade { old, new } => {
                self.release(&old);
                self.acquire(&new);
                self.try_grant_waiting();
            }
        }
    }

    /// Releases a [`ResourceAccessSet`] to make others able acquire it again.
    fn release(&mut self, resources: &ResourceAccessSet) {
        for (resource, access_mode) in resources {
            let lock_state = self
                .resource_accesses
                .get_mut(resource)
                .expect("resource should have been locked before");
            lock_state.release(access_mode);
            // NB: when all locks have been released, we can do 'garbage collection' on this lock
            // => remove the lock from the resource accesses map, to prevent garbage accumulation
            if lock_state.all_released() {
                self.resource_accesses.remove(resource);
            }
        }
    }

    /// Acquires a [`ResourceAccessSet`] to make others unable to acquire any conflicting locks.
    fn acquire(&mut self, resources: &ResourceAccessSet) {
        for (resource, access_mode) in resources {
            if let Some(lock_state) = self.resource_accesses.get_mut(resource) {
                // entry exists, just aquire by reference (cheap, frequent)
                lock_state.acquire(access_mode);
            } else {
                // entry not inserted yet, insert with cloning resource (expensive, rare)
                self.resource_accesses
                    .entry(resource.clone())
                    .or_default()
                    .acquire(access_mode);
            }
        }
    }

    /// Loop through every waiting request in the [`acquire_queue`], halting processing once
    /// reaching a barrier, i.e. once a queued request exceeds the [`max_skip_tolerance`] window.
    ///
    /// [`acquire_queue`]: Self::acquire_queue
    /// [`max_skip_tolerance`]: Self::max_skip_tolerance
    fn try_grant_waiting(&mut self) {
        let mut still_waiting = VecDeque::new();
        let mut barrier_active = false;
        while let Some(mut queued) = self.acquire_queue.pop_front() {
            // check if we hit a barrier prior to this (i.e. exceeded max skip tolerance window)
            if barrier_active {
                still_waiting.push_back(queued);
                continue;
            }

            // check if all resources can be locked
            let mut all_allowed = true;
            for (resource, access_mode) in queued.request.resources.iter() {
                if let Some(lock_state) = self.resource_accesses.get(resource)
                    && !lock_state.allows(access_mode)
                {
                    all_allowed = false;
                    break;
                }
            }

            // when not allowed, requeue and continue with next
            if !all_allowed {
                // if we reached the max skip count, activate barrier
                barrier_active = queued.skip_count >= self.max_skip_tolerance;
                // if we haven't reached the max skip count, increment skip count by one
                if !barrier_active {
                    queued.skip_count += 1;
                }
                // requeue this request for later processing
                still_waiting.push_back(queued);
                continue;
            }

            // lock the requested resources
            self.acquire(&queued.request.resources);

            // send back a guard that will free the resources on drop
            let guard = AccessGuard {
                resources: Some(queued.request.resources),
                tx_to_dispatcher: self.tx.clone(),
            };
            if let Err(mut guard) = queued.request.grant_tx.send(guard) {
                let resources = guard.resources.take().expect(
                    "the resources have not been freed yet, when not leaving the dispatcher",
                );
                self.release(&resources);
                std::mem::forget(guard);
            }
        }
        self.acquire_queue = still_waiting;
    }
}

/// Manages the access to all of the database objects within Tempest.
/// The management of these accesses happens through communication with the [`AccessDispatcher`],
/// which runs in a background tasks and listens for incoming messages through an async channel.
pub(crate) struct AccessManager {
    tx_to_dispatcher: mpsc::UnboundedSender<DispatcherMessage>,
}

impl AccessManager {
    pub(crate) async fn init(max_skip_tolerance: u32) -> Self {
        let (tx_to_dispatcher, rx_to_dispatcher) = mpsc::unbounded_channel();

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

        match rx.await {
            Ok(guard) => guard,
            Err(_recv_error) => {
                panic!("Channel closed: Resource access dispatcher has likely crashed!")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::*;

    macro_rules! resource_set {
        // Rule for Table
        (@res Table($db:expr, $table:expr)) => {
            Resource::Table($db.try_into().unwrap(), $table.try_into().unwrap())
        };
        // Rule for Database
        (@res Database($db:expr)) => {
            Resource::Database($db.try_into().unwrap())
        };
        // Rule for Catalog
        (@res Catalog) => {
            Resource::Catalog
        };

        // Rule for Modes
        (@mode IntentShared) => { AccessMode::IntentShared };
        (@mode IntentExclusive) => { AccessMode::IntentExclusive };
        (@mode Shared) => { AccessMode::Shared };
        (@mode Exclusive) => { AccessMode::Exclusive };

        // The entry point: matches "Table(a, b) => Exclusive, ..."
        ($($kind:ident $(($($args:expr),*))? => $mode:ident),* $(,)?) => {{
            let mut _set = ::std::collections::HashSet::new();
            $(
                let res = resource_set!(@res $kind $(($($args),*))?);
                let mode = resource_set!(@mode $mode);
                _set.insert((res, mode));
            )*
                _set
        }};
    }

    #[tokio::test]
    async fn test_access_manager() {
        let max_skip_tolerance = 64;
        let manager = AccessManager::init(max_skip_tolerance).await;
        let db = "main";
        let table = "users";

        let resources = resource_set![Table(db, table) => Shared];

        // 1. Hold an S-lock
        let shared_guard = manager.acquire(resources.clone()).await;

        // 2. Request X-lock: Will block due to 1. S-lock
        let exclusive_future = manager.acquire(resource_set![Table(db, table) => Exclusive]);
        tokio::pin!(exclusive_future);

        // Give the dispatcher a tiny window to put the X-Lock in the queue
        let sync_check =
            tokio::time::timeout(Duration::from_millis(5), &mut exclusive_future).await;
        assert!(
            sync_check.is_err(),
            "The X-Lock should not have been acquired yet"
        );

        // 3. Request Shared locks
        let mut shared_futures = Vec::new();
        // NB: Here we request one less, because the X-lock was already 'skipped' over once,
        // when it was denied the first time right above
        for _ in 0..max_skip_tolerance - 1 {
            shared_futures.push(manager.acquire(resources.clone()));
        }
        // it blocks here:
        let granted_shared = futures::future::join_all(shared_futures).await;
        assert_eq!(granted_shared.len(), max_skip_tolerance as usize - 1);

        // 4. Request Shared lock one more time; should time out
        let res = tokio::time::timeout(Duration::from_millis(20), manager.acquire(resources)).await;
        assert!(
            res.is_err(),
            "Barrier should have prevented jump-ahead over 2. lock (X)"
        );

        // 5. Drop 1. Shared lock, to allow for 2. Exclusive lock to be aquired
        drop(shared_guard);
        drop(granted_shared);
        let _exclusive_guard = tokio::time::timeout(Duration::from_millis(20), exclusive_future)
            .await
            .expect("after dropping 1. S-lock, the 2. X-lock should be acquired successfully");
    }
}
