# System and information functions (TODO 2.9)

These functions read the environment of the query: the server version, the session's user, database
and connection, and what earlier statements of the session did. A query cannot change them. The model
gives them as constants, like the current time (`statement_time`). They are collected in the record
`sys_env` of `src/data/dialects/SystemFuns.v`. Its value `default_env` describes a fresh session of
user `root` on database `test`, connection 1, after no insertion. Another session is obtained by
replacing `default_env`. Tests: `src/testing/Test_System.v`.

| Function | PostgreSQL | MySQL family | SQLite | Oracle mode | Value in `default_env` |
|---|---|---|---|---|---|
| `version()` | M | M | `sqlite_version()` M | — | `env_versions` per engine |
| user | `current_user`, `session_user`, `user`, `current_role` | `USER()`, `CURRENT_USER()`, `SESSION_USER()`, `SYSTEM_USER()` (`user@host`) | — | `USER`, `UID`, `SYS_CONTEXT('USERENV', …)` | `root` (`root@localhost`) |
| database / schema | `current_database()`, `current_catalog`, `current_schema` | `DATABASE()`, `SCHEMA()` | — | `SYS_CONTEXT('USERENV', 'DB_NAME')` | `test`, schema `public` |
| connection | `pg_backend_pid()` | `CONNECTION_ID()` | — | `SESSIONID` | 1 |
| effects of earlier statements | — | `LAST_INSERT_ID()` (with an argument: the argument), `ROW_COUNT()`, `FOUND_ROWS()` | `last_insert_rowid()`, `changes()`, `total_changes()` | — | 0, -1, 0 |

## Not modelled

These are excluded because they are nondeterministic or have side effects:

- `uuid()` and `uuid_short()`;
- `sleep()` and `benchmark()`, which are timing functions;
- `txid_current()` and the `pg_*` administration functions;
- `random()` (see TODO 2.1).

The PostgreSQL information functions that read the catalog are not modelled either (`has_*_privilege`,
`pg_get_*`, `obj_description`). The model has no catalog beyond the tables of the query.
