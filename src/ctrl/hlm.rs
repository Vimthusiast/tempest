//! # Hierarchical Lock Manager
//!
//! The HLM manages concurrent access to database resources by coordinating lock acquisition and
//! release across transactions. Rather than modeling the classic database/table/row hierarchy
//! explicitly, the HLM operates purely on key ranges - a table lock is just a wide range, a row
//! lock a degenerate range where start == end. The granularity is implicit in the range width,
//! not in an explicit hierarchy enum.
//!
//! ## Lock Modes
//!
//! Two lock modes are supported:
//!
//! - [`LockMode::Shared`] - multiple transactions may hold concurrently.
//! - [`LockMode::Exclusive`] - no concurrent access permitted.
//!
//! Intent locking is implicit in range width rather than a separate mode. A wide range S lock on
//! `[db|table|MIN]..[db|table|MAX]` behaves as an IS lock would in classic hierarchical locking
//! - it signals shared access at the table level without blocking unrelated row-level operations
//! outside the range.
//!
//! ## Key Range Encoding
//!
//! Lock targets are expressed as `[start, end)` byte ranges over the same keyspace used by the
//! silos. This means:
//!
//! ```not_rust
//! Database lock:  [db | MIN          ]  ..  [db | MAX          ]
//! Table lock:     [db | table | MIN  ]  ..  [db | table | MAX  ]
//! Row lock:       [db | table | pk   ]  ..  [db | table | pk   ]
//! Column range:   [db | table | col  | val_low ] .. [db | table | col | val_high]
//! ```
//!
//! The HLM itself has no schema knowledge - it operates on opaque byte ranges. Translation from
//! query predicates to key ranges is the responsibility of the query planner in
//! [`crate::ctrl::planner`].
//!
//! ## Secondary Indices
//!
//! Range locks on indexed columns are acquired on the secondary index keyspace for that column.
//! A secondary index entry has no meaningful value part - the column value and primary key are
//! encoded entirely in the key:
//!
//! ```not_rust
//! key:   [db | table | col_value | pk]
//! value: (empty)
//! ```
//!
//! A range lock on `col_age > 18` therefore becomes a range lock on the age secondary index
//! keyspace, which correctly blocks any insertion of a row with `age > 18` regardless of which
//! code path triggered the insert, since all writes must maintain secondary index consistency.
//!
//! Only indices actually touched by a query predicate require range locks. Unrelated indices are
//! untouched, giving maximum concurrency.
//!
//! We could go even further and implement predicate locking, to allow locking on unindexed columns
//! by storing the predicate itself alongside the interval. Conflict detection would then become a
//! two-phase process: first a geometric keyrange overlap check, then a predicate evaluation
//! against the conflicting entry's column predicates. For unindexed columns this falls back to a
//! table-wide range lock in the simple case, accepting reduced concurrency in exchange for
//! correctness. True predicate locking is left as a future extension - for now, queries on
//! unindexed columns acquire table-level range lock conservatively.
//!
//! Without predicate locking, our flow would look as simple as this:
//!
//! ```not_rust
//!  Query Predicate
//!          |
//!  Column indexed?
//!          |
//!     yes--+---no
//!     |         |
//!  Range     Table-wide
//!  lock on   range lock
//!  index     (fallback)
//!     |         |
//!     +----+----+
//!          |
//!  Geometric overlap check
//!  using an interval tree
//!          |
//!      conflict?
//!          |
//!   yes----+----no
//!    |           |
//!  Park on    Acquire lock,
//!  semaphore  increment counter
//! ```
//!
//! With predicate locking however, we have to consider a bit more, basically splitting the access
//! check into two phases: A range check, followed by evaluating the *inner* prediates.
//!
//! ```not_rust
//!  Query Predicate
//!          |
//!  Column indexed?
//!          |
//!     yes--+---no
//!     |         |
//!  Range     Table-wide
//!  lock on   range lock
//!  index     (fallback)
//!     |         |
//!     +----+----+
//!          |
//!  geometric overlap check
//!  using an interval tree
//!          |
//!       overlap?
//!          |
//!   yes----+-----no
//!    |           |
//!  predicate   Acquire lock,
//!  evaluation  increment counter
//!        |
//!     conflict?
//!        |
//!   yes--+-----no
//!    |          |
//!  Park on    Acquire lock,
//!  semaphore  increment counter
//! ```

// NB: I first should start out with an augmented BTreeMap, before moving to an interval tree.
// There is not really a good interval tree crate out there I like, so I'm gonna roll my own later.
