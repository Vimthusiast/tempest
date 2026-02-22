# Tempest DB

A modern database system that aims to reduce the pain I feel, everytime I have to do
anything that has to do with changing my schema or querying for data.

> [!IMPORTANT]
> This is just a learning project that is under development. Take every `Promise` you see here with
> caution, cause it may end up being `reject()`ed 😉 later. I mainly started this out, wanting to
> learn about distributed systems, after reading about how [CockroachDB] handles massive amounts of
> relational data in a flat key-value store called [Pebble]!

Old SQL-based database systems have...
- nullability by default (and the `NOT NULL` operator I despise),
- weird capitalized syntax (sucks to type and is not even required?!; clear style guidelines, please!),
- problems with managing migrations easily,
- don't business logic well to data schemas, often resulting in disgusting ORM abstractions.

## Current Progress

Tempest is currently in the **LSM-Storage Layer** phase:
* **Storage Silos:** Shared-nothing architecture using `io_uring` for high-performance I/O.
* **Hybrid Logical Clocks (HLC):** Maintaining causality across distributed silos.
* **Merging Engine:** A high-performance $k$-way merge iterator for read paths.
* **Zero-Overhead Tracing:** Logging is compiled out in release builds for maximum throughput.

I started out with prototypes that had lots of `lock()`s and `Arc`s all over the place, when I
wanted to test out `io_uring` and noticed the restriction on `!Send`. That was the moment I had to
rethink my architecture and moved away from a [CockroachDB] inspired multi-threaded implementation with
synchronization primitives all over the place towards a **Shared-nothing** approach, that has been proven
to be easier to get right (in some places!) as well as more performant, proven by modern system engineering
marvels, like [ScyllaDB] and the more recent [TigerBeetle].
I've also head that [Redpanda] uses the same architecture, to get 10x higher performance that the old [Kafka],
though it seems to be a JVM -> C++ advantage as well.

## TQL Syntax Examples

I am planning to implement my own query language called **TQL**, short for **Typed Query Language**,
with a big emphasis on the *Typed* part, since I'm writing this whole thing in **Rust** and that's
a language where types are kind of a big thing (`enum`s are always awesome, change my mind!).

This means I will try to implement a way to have custom type definitions, allowing for reusable
datatypes across the database. Maybe we could even attach methods to them, like custom sorting strategies!

Now, for the example:

```tql
create table users (
    username String,
    email String,
    age Optional(Int8),
     // ^ an optional field, that may be Some() 8-bit integer, or also None
    primary key (
        username,
        email,
          // ^ tql allows for trailing commas!
    ),
);

// Custom type definition: A matrix of different weight parameters.
create type WeightMatrix (Array(Array(Float32)));
```

Take a look at this *ugly SQL* for just a second:

```sql
CREATE TABLE users (
    username TEXT NOT NULL,
    email STRING NOT NULL,
    age INT,
    PRIMARY KEY (username, email,),
                             -- ^ ^ errors... why does SQL do this to us?!
);
```

Needless to say, I still take big inspiration from SQL, since I do like the overall ordering of
how the langauge puts its keywords. The command `create table` is really easy to understand!

[Pebble]: https://github.com/cockroachdb/pebble
[CockroachDB]: https://github.com/cockroachdb/cockroach
[ScyllaDB]: https://github.com/scylladb/scylladb
[TigerBeetle]: https://github.com/tigerbeetle/tigerbeetle
[Redpanda]: https://github.com/redpanda-data/redpanda
[Apache Kafka]: https://github.com/apache/kafka
