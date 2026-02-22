# Tempest



```tql
create table users (
    username String,
    email String,
    age Optional(Int8),
              // ^ 8 byte integer (not bits)
    primary key (
        username,
        email,
          // ^ allows trailing commas!
    ),
  // ^ another trailing comma
);

create type matrix (Array(Array(Int8)))
```

```sql
CREATE TABLE users (
    username TEXT NOT NULL,
    email STRING NOT NULL,
    age INT,
    PRIMARY KEY (username, email,),
                             -- ^ ^ errors... why does SQL do this to us?!
);
```

