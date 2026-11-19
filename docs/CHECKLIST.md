# Checklist: what a complete formal semantics of SQL queries still needs

Goal: a complete formal semantics of the query language of PostgreSQL, MySQL, SQLite, OceanBase
(MySQL and Oracle modes), MariaDB, TiDB, Percona Server and PolarDB, with a common core and one
description per dialect. `[x]` is done (tested in the build), `[~]` partly done, `[ ]` not done.
This file replaces the status columns of `OPEN_ISSUES.md` I9 as the master list; each pull request
updates it.

## A. Core: constructs of the query language (`SqlFull.v`)

- [x] `SELECT` blocks: `DISTINCT`, `WHERE`, `GROUP BY`, `HAVING`, implicit single group
- [x] Joins: inner, left, right, full, cross, `LATERAL`; `NATURAL` (derived form)
- [x] Set operations `UNION`/`INTERSECT`/`EXCEPT`, with and without `ALL`
- [x] `ORDER BY` (direction, `NULLS FIRST/LAST`), `OFFSET`, `LIMIT`, `FETCH FIRST ... [WITH TIES] [PERCENT]`
- [x] Subqueries: scalar, `EXISTS`, `IN`, `ANY`/`ALL`, correlated; aggregate home block
- [x] `WITH`, `WITH RECURSIVE` (fuel-bounded)
- [x] `VALUES`
- [x] Window functions: aggregates, `ROW_NUMBER`, `RANK`, `DENSE_RANK`, `NTILE`, `PERCENT_RANK`, `CUME_DIST`,
      `LAG`, `LEAD`, `FIRST_VALUE`, `LAST_VALUE`, `NTH_VALUE`; frames `ROWS`, `GROUPS`, `RANGE` with integer offsets
- [x] `GROUPING SETS`, `ROLLUP`, `CUBE`, `GROUPING()`
- [x] `FILTER (WHERE ...)`, `DISTINCT` aggregates, aggregates with `ORDER BY` and separator
- [x] `DISTINCT ON` (derived form)
- [ ] Window: frame exclusion (`EXCLUDE CURRENT ROW/GROUP/TIES`), `RANGE` with decimal/interval offsets, named windows,
      `IGNORE NULLS` / `RESPECT NULLS`, `FROM LAST`, `NTH_VALUE` variants, window functions in `ORDER BY` / aggregate windows over `DISTINCT`
- [ ] Ordered-set and hypothetical-set aggregates: `percentile_cont`, `percentile_disc`, `mode`, `rank(...) WITHIN GROUP`, `MEDIAN`
- [ ] Other multi-argument aggregates (`corr`, `covar_*`, `regr_*`, `string_agg` with `DISTINCT`), `array_agg`, `json_agg`, `json_arrayagg`, `json_objectagg`
- [ ] `USING` joins (column merging), `JOIN ... USING` with outer joins and `SELECT *` expansion
- [ ] Table functions in `FROM`: `generate_series`, `unnest`, `json_table`, `JSON_TABLE`, `XMLTABLE`, `OPENJSON`-like, SQLite virtual tables
- [ ] `TABLE t`, `SELECT ... FROM DUAL`, `SELECT` without `FROM`, `VALUES` as a statement with `ORDER BY`
- [ ] `GROUP BY` / `ORDER BY` by ordinal position and by output alias; `HAVING` on aliases (MySQL, SQLite)
- [ ] Set operation precedence, parenthesised queries, `ORDER BY`/`LIMIT` on each operand, column name and type resolution of `UNION`
- [ ] Mutual and multiple recursion, `SEARCH` / `CYCLE` clauses (PostgreSQL), recursion limits (`cte_max_recursion_depth`, per engine)
- [ ] Row values: row comparison `(a, b) < (c, d)` outside `IN`, `ROW()` constructors, `OVERLAPS`
- [ ] `SELECT ... INTO`, `FOR UPDATE` / locking clauses (no effect on results, must be accepted and ignored explicitly)
- [ ] Optimizer hints and their (absent) effect on results
- [ ] Output column naming (derived names of unnamed expressions), duplicate column names (I4: positional semantics)
- [ ] Views, `INFORMATION_SCHEMA` / catalog queries (as tables with the engine's contents)
- [ ] Non-determinism: `RANDOM`, `NOW`, session variables, `LIMIT` without `ORDER BY`, ties in `ORDER BY`, bare columns (a set of results, not one)
- [x] Errors as results (I3): division by zero, invalid casts, scalar subquery returning several rows, recursion limits (TODO 1.1); overflow with 1.2.3

## B. Values and types (the dialect-specific heart)

- [~] Numbers: integers and exact rationals (done); **decimal scale and precision** ([ ]), **IEEE floats** (`float4/8`, `NaN`, `Infinity`, `-0`, rounding) ([ ]),
      integer ranges and overflow (`TINYINT` .. `BIGINT`, `UNSIGNED`) ([ ]), `numeric(p,s)` rounding on cast ([ ])
- [~] Strings: byte-wise and case-insensitive/`PAD SPACE` collations (done); **accent folding and `utf8mb4_0900_ai_ci`, `utf8mb4_unicode_ci`,
      `uca1400`, PostgreSQL locale/ICU collations, `COLLATE` clauses and collation precedence** ([ ]); charsets and encodings, `BINARY` strings, `bytea`, blobs ([ ]);
      `CHAR(n)` vs `VARCHAR(n)` padding and length limits ([ ])
- [ ] Booleans of each dialect (real boolean in PostgreSQL, 0/1 in MySQL/SQLite, none in Oracle mode)
- [ ] Dates and times: `DATE`, `TIME`, `TIMESTAMP[TZ]`, `DATETIME`, `YEAR`, `INTERVAL`, time zones, calendar arithmetic, `EXTRACT`, `DATE_TRUNC`,
      `DATE_ADD`, `STR_TO_DATE`, `TO_CHAR`, SQLite date functions (strings/numbers), Oracle `DATE` with time
- [ ] JSON: types, operators (`->`, `->>`, `@>`), path languages (`JSONPath`, MySQL path), `JSON_TABLE`, comparison and ordering of JSON values
- [ ] Arrays, composite types, ranges, enums, `UUID`, `INET`, geometric and spatial types, full-text (`MATCH ... AGAINST`, `tsvector`), `BIT`, `SET`/`ENUM` (MySQL)
- [ ] SQLite dynamic typing: type affinity, storage classes in all operations (comparison done; arithmetic, `CAST`, `typeof` partly)
- [ ] Implicit conversions between all type pairs per dialect (string/number/date/boolean), including MySQL's warnings-versus-errors under `sql_mode`
- [ ] `CAST` / `CONVERT` / `::` to every type, with each dialect's parsing rules
- [ ] `sql_mode` as a parameter: `ANSI_QUOTES`, `PIPES_AS_CONCAT`, `ONLY_FULL_GROUP_BY`, `STRICT_*`, `NO_BACKSLASH_ESCAPES`, `PAD_CHAR_TO_FULL_LENGTH`, `ORACLE` (MariaDB)

## C. Predicates, operators and functions, per dialect

The tables have 40-60 entries per dialect; each engine has several hundred. For **every** dialect
(PostgreSQL, MySQL, MariaDB, TiDB, Percona, PolarDB, SQLite, OceanBase MySQL, OceanBase Oracle) the missing families are:

- [ ] Arithmetic and math: `mod`, `div`, `sqrt`, `exp`, `ln`, `log`, `sin`..., `pi`, `rand`, `ceiling`, `bit` operators, shifts, `width_bucket`, `gcd`/`lcm`
- [ ] String: `lower`, `substring_index`, `lpad`/`rpad`, `format`, `translate`, `initcap`, `ascii`/`chr`, `split_part`, `regexp_*`, `similar to`, `ilike`,
      `like ... escape`, `soundex`, `hex`/`unhex`, `md5`/`sha*`, `to_base64`, `concat` variants, `overlay`, `quote_*`, `char`/`ord`
- [ ] Comparison and logic: `in (list)` NULL cases, `between symmetric`, `<=>`, `is distinct from` in every dialect, `exists`, `any/all` operators, `xor`
- [ ] Conditionals: `case` (simple/searched), `decode` (Oracle), `if`, `iif`, `nvl*`, `coalesce` with type resolution
- [ ] Date/time functions (see B)
- [ ] Regular expressions: `~`, `REGEXP`, `REGEXP_LIKE/REPLACE/SUBSTR/INSTR`, flags, the three regex dialects (POSIX/ARE, ICU/Henry Spencer, Oracle)
- [ ] JSON, array, range functions (see B)
- [ ] System and session functions (`version()`, `current_user`, `database()`), `last_insert_id`
- [ ] Per-dialect function-name aliases and absent functions, argument-count and type checking (accept/reject), not only names
- [ ] Aggregates: the full list per dialect (`bit_xor`, `std*`, `stddev*`, `any_value`, `array_agg`, `json_*agg`, `count(distinct a, b)`, `approx_*`)
- [ ] Null handling and empty-group results of every aggregate, `DISTINCT` plus `FILTER` plus `ORDER BY` combinations

## D. Dialect fidelity

- [x] PostgreSQL, MySQL, SQLite, OceanBase MySQL: constructs, comparison, division, concatenation, `LIKE`, aggregates (checked on sqllogictest / OceanBase `mysql_test`)
- [~] OceanBase Oracle mode: from documentation and shared source; **no recorded results available**
- [~] MariaDB, TiDB, Percona, PolarDB: constructs, default collation, `sql_mode`; **their own functions, types and conversion rules are not modelled**;
      TiDB's new-collation framework; MariaDB `sql_mode=ORACLE`; PolarDB-X and the PostgreSQL/Oracle editions of PolarDB; TiDB `tidb_*` variables that change semantics
- [ ] Oracle database itself, SQL Server, DuckDB, ClickHouse, CockroachDB, Snowflake, BigQuery (not in the target list; list here to decide)
- [ ] Per-version differences: MySQL 5.7 vs 8.0 vs 8.4, PostgreSQL 12..17, SQLite 3.x, MariaDB 10/11/12, TiDB 6/7/8, OceanBase 3/4 (feature flags per version)
- [~] Session/system variables that change query results: MySQL family done (`sql_mode` flags `PIPES_AS_CONCAT`, `ONLY_FULL_GROUP_BY`, `div_precision_increment`, `group_concat_max_len`, collation); `time_zone`, float display, `tidb_*`, `ob_*`, MariaDB `ORACLE` mode to come
- [ ] Bare columns in aggregate queries: the value (SQLite's row of `min`/`max`, MySQL/MariaDB arbitrary row), as a set of allowed results
- [ ] Functional dependencies for `ONLY_FULL_GROUP_BY` (keys, `PRIMARY KEY`, `UNIQUE NOT NULL`), checks inside subqueries

## E. Validation against real engines

- [x] sqllogictest for SQLite, PostgreSQL, MySQL, OceanBase MySQL (random expressions, selects, groupby, aggregates); OceanBase `mysql_test` (545 queries)
- [ ] Conformance runs for MariaDB, TiDB, Percona, PolarDB (their test suites: MariaDB `mysql-test`, TiDB `tests/integrationtest`, MySQL `mysql-test`, PostgreSQL `regress`)
- [ ] PostgreSQL regression suite (`src/test/regress`), SQLite TCL tests, MySQL `mysql-test` translated and run
- [ ] Differential testing against live engines (needs engines in the environment; not available in the cloud sandbox now)
- [ ] Window, `WITH`, `GROUPING SETS`, `RECURSIVE`, ordered aggregates in the translator (the semantics has them; no recorded results are translated)
- [ ] The bugs found by ValScope and Pinolo (MySQL, MariaDB, TiDB, OceanBase, Percona, PolarDB) as regression cases: each reported bug's query with the expected (correct) result
- [ ] Remaining failures of OceanBase (6 queries: decimal scale, internal precision)

## F. Metatheory and quality of the formalisation

- [ ] Relate `SqlFull.v` to the existing `Sql.v`/algebra (I2): a theorem that the fragment agrees; fix `Sql.v` deviations (A4, A6)
- [ ] Well-formedness and typing of queries (I5): sort checking, aggregate placement, scope of columns, ambiguity; static rejection per dialect
- [ ] Positional semantics (I4) instead of named tuples; duplicate column names; `SELECT *` over joins
- [ ] Properties proved about the semantics: termination and determinism of evaluation, `DISTINCT`/set-operation laws, join identities, window-frame laws, grouping-set laws, dialect refinement (`to_dialect` is identity up to types)
- [ ] Proofs that rewrite rules used by DBMS testing tools (`WHERE p` partitioning into `p`, `NOT p`, `p IS NULL`; containment relations of Pinolo; value-semantics rules of ValScope) hold in the model for each dialect
- [ ] `FreshAttr.v` (`Admitted`)
- [ ] A SQL text frontend: lexer/parser/printer for each dialect to Coq syntax (the Python translators are a partial stand-in); pretty printer of results
- [ ] Extraction or a verified executable (OCaml) interpreter so the model can be run on large inputs
- [ ] Performance of the Coq evaluation (`vm_compute` on large tables)
- [ ] Documentation: a per-dialect semantics manual generated from the tables, with source references for every entry

## G. Process

- [x] Every gap and decision is recorded in this repository and in PRs (`OPEN_ISSUES.md`, PR #1 comments)
- [ ] CI runs the whole build and all conformance samples on every pull request (build workflow exists; conformance samples are in the build)
- [ ] A per-entry provenance record: for every function/predicate/aggregate/type rule, which source file or document establishes it
