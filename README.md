# Tempest DB

[![wakatime](https://wakatime.com/badge/github/Vimthusiast/tempest.svg)](https://wakatime.com/badge/github/Vimthusiast/tempest)

Tempest is a distributed database built around one principle: **the type system should do the
work** - no implicit nulls, no surprise migrations, no mismatch between your schema and your
application types.

> [!IMPORTANT]
> This is a learning project under active development. I'm 16, still in high school, and built this
> after going down a rabbit hole reading about how [CockroachDB] handles relational data on top of a
> flat key-value store ([Pebble]). It's ambitious, possibly foolish, and I'm enjoying every second.
> Take any `Promise` here with caution - it may yet be `reject()`ed ??

---

## The Problem With SQL

SQL's type system puts the burden in the wrong place.

**Nullability is opt-out, not opt-in.** Every column silently accepts `NULL` unless you remember
to write `NOT NULL`. The result is that your schema lies - a column typed `INT` might actually
be empty, and your application has to defensively handle that everywhere.

**Adding a column is a footgun.** In SQL, `ALTER TABLE users ADD COLUMN bio TEXT NOT NULL` fails
on existing rows because it can't produce a value retroactively. The workaround - a `DEFAULT ''` -
fills your database with empty strings that mean "unknown." That's not a default, it's a lie
dressed up as one.

**Migrations are managed outside the database.** SQL has no built-in concept of schema history.
Tools like Flyway, Alembic, and Rails migrations exist entirely because SQL can't track its own
evolution. Your schema and your migration scripts are two separate sources of truth that can
quietly drift apart.

**The ORM exists to paper over all of this.** When your schema doesn't map cleanly to your
application types, you need a translation layer. That layer adds complexity, hides what's
actually happening in the database, and is often the first thing blamed when something goes
wrong.

---

## TQL: Typed Query Language

TQL is Tempest's query language. The core idea is that types are first-class citizens - defined
independently, reusable across the schema, and capable of carrying their own validation and
ordering logic.

### Types and Tables are separate things

A `type` defines the shape of data. A `table` attaches storage to a type. This means types can
be embedded, reused, and referenced independently of any particular table.

```tql
// Types are PascalCase, defined independently of storage
type Address {
    street  : String,
    city    : String,
    country : String,
}

type User {
    id       : Int64,
    username : String,
    email    : String,
    age      : Int8?,     // `?` suffix = Optional - may be Some(value) or None
    address  : Address,   // embedded type, no join required
}

// `create table` attaches storage to a type
create table users : User {
    primary key (id),
}
```

The rule is simple: **user-defined types are PascalCase, builtins are lowercase, and `:` always
means "has type."** At a glance, you know what's yours and what's built in.

### Optional is honest about absence

`Int8?` is shorthand for `Optional(Int8)` - a value that is explicitly either `Some(x)` or
`None`. There is no implicit null. If a field can be absent, the type says so, and the query
language requires you to handle it.

```tql
// Pattern-match style: filter and bind in one step
select id, username
from   users
where  age? > 18;
//       ^ `?` in a query unwraps the Optional,
//         implicitly filtering out rows where age is None
```

For cases where you want to handle `None` explicitly:

```tql
select id, username, age
from   users
where  age is Some(a) and a > 18;
//              ^ binds the inner value to `a` only when present
```

### Migrations that can't lie

Because new columns are `Optional` by default, adding a column to an existing table is always
safe - existing rows get `None`, which is honest rather than a fabricated default.

```tql
// Safe to run on a table with existing rows:
// existing rows get None for `bio`, not an empty string
alter table users add column bio String?;
```

Renaming a column is a first-class operation tracked in the schema history, not two separate
migrations with a risky window in between:

```tql
alter table users rename column username to handle;
```

Because Tempest's manifest already records schema history, the database itself is the source of
truth for how the schema has evolved - no external migration tool required.

### Custom types with behaviour

Types can carry validation logic and custom ordering strategies, which map directly onto the
storage layer's comparator infrastructure:

```tql
type EmailAddress(String) {
    // Validates on insert; returns None if the value is malformed
    fn new(raw: String) -> EmailAddress? {
        match raw.contains("@") {
            true  => Some(EmailAddress(raw)),
            false => None,
        }
    }

    // Custom ordering: sort by domain, then by local part
    fn compare(a: EmailAddress, b: EmailAddress) -> Ordering {
        a.split("@")[1].compare(b.split("@")[1])
    }
}

type User {
    id    : Int64,
    email : EmailAddress,   // validation happens automatically on insert
}

create table users : User {
    primary key (id),
}

// Uses the custom `compare` defined on EmailAddress
select id, email from users order by email;
```

---

## Current Progress

- **Storage Silos** - Shared-nothing architecture using `io_uring` for async I/O without
  synchronization primitives. Inspired by [ScyllaDB] and [TigerBeetle].
- **LSM-Tree Storage** - Manifest, MemTable, and WAL complete. SST implementation in progress.
- **Hybrid Logical Clocks (HLC)** - Causality tracking across distributed silos, encoded
  directly into key suffixes for efficient ordering at the storage layer.
- **Iterator Layer** - k-way merge iterators for the read path, collecting across MemTable
  and SST sources.
- **TQL** - Design in progress. Parser and type system not yet implemented.

### Architecture note

Early prototypes used `Arc` and `Mutex` everywhere. When I started working with `io_uring` and
hit the `!Send` restriction, I had to rethink the whole thing. That forced a move to a
**shared-nothing architecture** - each silo owns its data and communicates via message passing,
no locks required. It turned out to be both easier to reason about and more performant, which is
the same bet [ScyllaDB], [TigerBeetle], and [Redpanda] make against their locked counterparts.

---

[Pebble]: https://github.com/cockroachdb/pebble
[CockroachDB]: https://github.com/cockroachdb/cockroach
[ScyllaDB]: https://github.com/scylladb/scylladb
[TigerBeetle]: https://github.com/tigerbeetle/tigerbeetle
[Redpanda]: https://github.com/redpanda-data/redpanda
[Apache Kafka]: https://github.com/apache/kafka
