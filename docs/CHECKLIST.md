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
- [x] Window: frame exclusion (`EXCLUDE CURRENT ROW/GROUP/TIES`), `RANGE` with decimal/interval offsets, named windows, (TODO 3.1: exclusion, RANGE offsets, named windows)
      `IGNORE NULLS` / `RESPECT NULLS`, `FROM LAST`, `NTH_VALUE` variants, window functions in `ORDER BY` / aggregate windows over `DISTINCT`
- [x] Ordered-set and hypothetical-set aggregates: `percentile_cont`, `percentile_disc`, `mode`, `rank(...) WITHIN GROUP`, `MEDIAN` (Aggregates.v, Test_OrderedSet)
- [x] Other multi-argument aggregates (`corr`, `covar_*`, `regr_*`, `string_agg` with `DISTINCT`), `array_agg`, `json_agg`, `json_arrayagg`, `json_objectagg` (Aggregates.v stat2, JSON aggregates)
- [x] `USING` joins (column merging), `JOIN ... USING` with outer joins and `SELECT *` expansion (translator and Test_Joins)
- [~] Table functions in `FROM`: `generate_series`, `unnest`, `json_table`, `JSON_TABLE`, `XMLTABLE`, `OPENJSON`-like, SQLite virtual tables (generate_series, unnest, json_each, JSON_TABLE done; XMLTABLE excluded)
- [x] `TABLE t`, `SELECT ... FROM DUAL`, `SELECT` without `FROM`, `VALUES` as a statement with `ORDER BY` (TODO 3.4, 5.1)
- [x] `GROUP BY` / `ORDER BY` by ordinal position and by output alias; `HAVING` on aliases (MySQL, SQLite) (translator subst_deep)
- [x] Set operation precedence, parenthesised queries, `ORDER BY`/`LIMIT` on each operand, column name and type resolution of `UNION` (Test_SetOps, translator precedence)
- [~] Mutual and multiple recursion, `SEARCH` / `CYCLE` clauses (PostgreSQL), recursion limits (`cte_max_recursion_depth`, per engine) (recursive aggregates done; SEARCH/CYCLE open)
- [x] Row values: row comparison `(a, b) < (c, d)` outside `IN`, `ROW()` constructors, `OVERLAPS` (Test_Rows)
- [x] `SELECT ... INTO`, `FOR UPDATE` / locking clauses (no effect on results, must be accepted and ignored explicitly) (TODO 3.11)
- [x] Optimizer hints and their (absent) effect on results (hints are comments: no effect, recorded in DIALECTS.md)
- [~] Output column naming (derived names of unnamed expressions), duplicate column names (I4: positional semantics) (Naming.v for PostgreSQL; duplicates wait for I4)
- [~] Views, `INFORMATION_SCHEMA` / catalog queries (as tables with the engine's contents) (views as derived tables in the translator; catalogs excluded)
- [~] Non-determinism: `RANDOM`, `NOW`, session variables, `LIMIT` without `ORDER BY`, ties in `ORDER BY`, bare columns (a set of results, not one) (ties and LIMIT done (TODO 3.10); RANDOM excluded)
- [x] Errors as results (I3): division by zero, invalid casts, scalar subquery returning several rows, recursion limits (TODO 1.1); overflow with 1.2.3

## B. Values and types (the dialect-specific heart)

- [~] Numbers: integers and exact rationals (done); decimal scale ([x], TODO 1.2.1), IEEE floats ([x], TODO 1.2.2),
      integer ranges and overflow ([x], TODO 1.2.3), `numeric(p,s)` rounding on cast ([x])
- [~] Strings: collations from the engines' tables (`general_ci`, `0900_ai_ci`, `unicode_520_ci`, `unicode_ci`, `bin`, SQLite, `C`), accents and expansions, `COLLATE` and explicit precedence ([x], TODO 1.3); `uca1400` (approximated), PostgreSQL ICU/libc, column collations ([ ]); charsets and encodings, `BINARY` strings, `bytea`, blobs ([ ]);
      `CHAR(n)` vs `VARCHAR(n)` padding and length limits ([ ])
- [x] Booleans of each dialect (real boolean in PostgreSQL, 0/1 in MySQL/SQLite, none in Oracle mode) (TODO 1.4)
- [~] Dates and times (TODO 1.5 done: types, arithmetic, `EXTRACT`, `DATE_TRUNC`, formats, SQLite and Oracle; open: time zones, `YEAR` type): `DATE`, `TIME`, `TIMESTAMP[TZ]`, `DATETIME`, `YEAR`, `INTERVAL`, time zones, calendar arithmetic, `EXTRACT`, `DATE_TRUNC`,
      `DATE_ADD`, `STR_TO_DATE`, `TO_CHAR`, SQLite date functions (strings/numbers), Oracle `DATE` with time
- [~] JSON (TODO 1.6 done for the three families; open: wildcards, modification functions, `JSON_TABLE`, SQL/JSON path): types, operators (`->`, `->>`, `@>`), path languages (`JSONPath`, MySQL path), `JSON_TABLE`, comparison and ordering of JSON values
- [~] Arrays, composite types, ranges, enums, `UUID`, `INET`, geometric and spatial types, full-text (`MATCH ... AGAINST`, `tsvector`), `BIT`, `SET`/`ENUM` (MySQL) (PostgreSQL arrays modelled; the other types excluded with reasons in docs/closeouts)
- [~] SQLite dynamic typing (TODO 1.8: affinity in comparisons done): type affinity, storage classes in all operations (comparison done; arithmetic, `CAST`, `typeof` partly)
- [~] Implicit conversions between all type pairs per dialect (string/number/date/boolean), including MySQL's warnings-versus-errors under `sql_mode` (per dialect in Values.v, MySQL.v, SQLite.v)
- [~] `CAST` / `CONVERT` / `::` to every type, with each dialect's parsing rules (casts of the modelled types)
- [~] `sql_mode` as a parameter: `ANSI_QUOTES`, `PIPES_AS_CONCAT`, `ONLY_FULL_GROUP_BY`, `STRICT_*`, `NO_BACKSLASH_ESCAPES`, `PAD_CHAR_TO_FULL_LENGTH`, `ORACLE` (MariaDB) (PIPES_AS_CONCAT, ONLY_FULL_GROUP_BY modelled; the others lexical or without effect on SELECT)

## C. Predicates, operators and functions, per dialect

The tables have 40-60 entries per dialect; each engine has several hundred. For **every** dialect
(PostgreSQL, MySQL, MariaDB, TiDB, Percona, PolarDB, SQLite, OceanBase MySQL, OceanBase Oracle) the missing families are:

- [x] Arithmetic and math: `mod`, `div`, `sqrt`, `exp`, `ln`, `log`, `sin`..., `pi`, `rand`, `ceiling`, `bit` operators, shifts, `width_bucket`, `gcd`/`lcm` (TODO 2.1, docs/functions/math.md)
- [x] String: `lower`, `substring_index`, `lpad`/`rpad`, `format`, `translate`, `initcap`, `ascii`/`chr`, `split_part`, `regexp_*`, `similar to`, `ilike`, (TODO 2.2)
      `like ... escape`, `soundex`, `hex`/`unhex`, `md5`/`sha*`, `to_base64`, `concat` variants, `overlay`, `quote_*`, `char`/`ord`
- [x] Comparison and logic: `in (list)` NULL cases, `between symmetric`, `<=>`, `is distinct from` in every dialect, `exists`, `any/all` operators, `xor` (TODO 2.3)
- [x] Conditionals: `case` (simple/searched), `decode` (Oracle), `if`, `iif`, `nvl*`, `coalesce` with type resolution (TODO 2.3)
- [x] Date/time functions (see B) (TODO 2.7)
- [x] Regular expressions: `~`, `REGEXP`, `REGEXP_LIKE/REPLACE/SUBSTR/INSTR`, flags, the three regex dialects (POSIX/ARE, ICU/Henry Spencer, Oracle) (TODO 2.4)
- [~] JSON, array, range functions (see B) (JSON and arrays done; ranges excluded)
- [x] System and session functions (`version()`, `current_user`, `database()`), `last_insert_id` (SystemFuns.v)
- [x] Per-dialect function-name aliases and absent functions, argument-count and type checking (accept/reject), not only names (Arity.v, docs/closeouts)
- [x] Aggregates: the full list per dialect (`bit_xor`, `std*`, `stddev*`, `any_value`, `array_agg`, `json_*agg`, `count(distinct a, b)`, `approx_*`) (docs/closeouts)
- [~] Null handling and empty-group results of every aggregate, `DISTINCT` plus `FILTER` plus `ORDER BY` combinations (Test_Aggregates)

## D. Dialect fidelity

- [x] PostgreSQL, MySQL, SQLite, OceanBase MySQL: constructs, comparison, division, concatenation, `LIKE`, aggregates (checked on sqllogictest / OceanBase `mysql_test`)
- [~] OceanBase Oracle mode: from documentation and shared source; **no recorded results available**
- [~] MariaDB, TiDB, Percona, PolarDB: constructs, default collation, `sql_mode`; **their own functions, types and conversion rules are not modelled**;
      TiDB's new-collation framework; MariaDB `sql_mode=ORACLE`; PolarDB-X and the PostgreSQL/Oracle editions of PolarDB; TiDB `tidb_*` variables that change semantics
- [~] Oracle database itself, SQL Server, DuckDB, ClickHouse, CockroachDB, Snowflake, BigQuery (not in the target list; list here to decide) (decision record D1 in OPEN_ISSUES.md, awaiting an answer)
- [x] Per-version differences: MySQL 5.7 vs 8.0 vs 8.4, PostgreSQL 12..17, SQLite 3.x, MariaDB 10/11/12, TiDB 6/7/8, OceanBase 3/4 (feature flags per version) (Versions.v)
- [~] Session/system variables that change query results: MySQL family done (`sql_mode` flags `PIPES_AS_CONCAT`, `ONLY_FULL_GROUP_BY`, `div_precision_increment`, `group_concat_max_len`, collation); `time_zone`, float display, `tidb_*`, `ob_*`, MariaDB `ORACLE` mode to come
- [~] Bare columns in aggregate queries: the value (SQLite's row of `min`/`max`, MySQL/MariaDB arbitrary row), as a set of allowed results (F_Bare_Column accepted; the value is not a set of results yet)
- [ ] Functional dependencies for `ONLY_FULL_GROUP_BY` (keys, `PRIMARY KEY`, `UNIQUE NOT NULL`), checks inside subqueries

## E. Validation against real engines

- [x] sqllogictest for SQLite, PostgreSQL, MySQL, OceanBase MySQL (random expressions, selects, groupby, aggregates); OceanBase `mysql_test` (545 queries)
- [~] Conformance runs for MariaDB, TiDB, Percona, PolarDB (their test suites: MariaDB `mysql-test`, TiDB `tests/integrationtest`, MySQL `mysql-test`, PostgreSQL `regress`) (TODO 5.2: MariaDB, TiDB, MySQL suites run (docs/CONFORMANCE.md); Percona and PolarDB have no open suite)
- [~] PostgreSQL regression suite (`src/test/regress`), SQLite TCL tests, MySQL `mysql-test` translated and run (PostgreSQL regression suite (TODO 5.3) and MySQL mysql-test run; SQLite TCL tests not replayable)
- [~] Differential testing against live engines (needs engines in the environment; not available in the cloud sandbox now) (not possible here: no engines in the environment)
- [x] Window, `WITH`, `GROUPING SETS`, `RECURSIVE`, ordered aggregates in the translator (the semantics has them; no recorded results are translated) (TODO 5.1)
- [ ] The bugs found by ValScope and Pinolo (MySQL, MariaDB, TiDB, OceanBase, Percona, PolarDB) as regression cases: each reported bug's query with the expected (correct) result
- [x] Remaining failures of OceanBase (6 queries: decimal scale, internal precision) (769/770, the last one runs in the extracted interpreter)

## F. Metatheory and quality of the formalisation

- [ ] Relate `SqlFull.v` to the existing `Sql.v`/algebra (I2): a theorem that the fragment agrees; fix `Sql.v` deviations (A4, A6)
- [ ] Well-formedness and typing of queries (I5): sort checking, aggregate placement, scope of columns, ambiguity; static rejection per dialect
- [ ] Positional semantics (I4) instead of named tuples; duplicate column names; `SELECT *` over joins
- [~] Properties proved about the semantics: termination and determinism of evaluation, `DISTINCT`/set-operation laws, join identities, window-frame laws, grouping-set laws, dialect refinement (`to_dialect` is identity up to types) (TODO 6.4: join, union, logic laws)
- [ ] Proofs that rewrite rules used by DBMS testing tools (`WHERE p` partitioning into `p`, `NOT p`, `p IS NULL`; containment relations of Pinolo; value-semantics rules of ValScope) hold in the model for each dialect
- [x] `FreshAttr.v` (`Admitted`) (TODO 6.5)
- [~] A SQL text frontend: lexer/parser/printer for each dialect to Coq syntax (the Python translators are a partial stand-in); pretty printer of results (tools/spec/sql2coq.py per dialect)
- [~] Extraction or a verified executable (OCaml) interpreter so the model can be run on large inputs (TODO 6.6: extraction checked on the OceanBase corpus)
- [~] Performance of the Coq evaluation (`vm_compute` on large tables) (the extracted program: 48 s for the OceanBase corpus)
- [~] Documentation: a per-dialect semantics manual generated from the tables, with source references for every entry (docs/functions, docs/closeouts, docs/guides)

## G. Process

- [x] Every gap and decision is recorded in this repository and in PRs (`OPEN_ISSUES.md`, PR #1 comments)
- [~] CI runs the whole build and all conformance samples on every pull request (build workflow exists; conformance samples are in the build) (build, provenance and hygiene checks in CI; conformance runs need the engines' suites)
- [~] A per-entry provenance record: for every function/predicate/aggregate/type rule, which source file or document establishes it (tools/functions/check_provenance.py for the function tables)
