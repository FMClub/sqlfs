# SQL dialects

The goal is one formal semantics of the query language of SQL which covers the
mainstream relational systems: PostgreSQL, MySQL, SQLite, OceanBase (in its
MySQL and Oracle modes), and the MySQL family tested by recent logical-bug detection work
(ValScope, OSDI 2026; Pinolo, ATC 2023): MariaDB, TiDB, Percona Server and PolarDB. They agree on the structure of queries and on
three-valued logic, and differ in many details. This document says how the
differences are organised, what is done, and what is planned.

## Architecture

A dialect has two parts.

1. **The engine-level part**, the record `dialect` of `src/data/sql/SqlFull.v`,
   which parameterises the evaluation of queries:
   - `canon`: the key of a value for the operations which identify values that are
     not distinct without being equal (`GROUP BY`, `DISTINCT`, set operations,
     `DISTINCT` aggregates). The identity for byte-wise string comparison; a case
     folding for a case-insensitive collation.
   - `order`, `eq3`: the comparison used by `ORDER BY`, window frames and `IN`.
   - `nulls_smallest`: where `ORDER BY` puts the NULLs by default.
   - `truth_of_value`, `value_of_truth`: how a condition is turned into a value and
     back (a boolean in PostgreSQL, 0/1 in MySQL and SQLite).
   - `supports`: the constructs of the language which the dialect accepts
     (`feature`); `accepted_by d q` checks a query.
2. **The value-level part**, an instance of `Tuple.Rcd`: the type of values, and the
   interpretation of the predicates, of the function symbols and of the aggregates
   (implicit conversions, arithmetic, division, string functions, `LIKE`,
   concatenation, NULL handling of aggregates, ...). `Values.v` is the
   PostgreSQL-like base; the other dialects are in `src/data/dialects/`.

## Where the dialects differ

`done` means that it is modelled and tested: the engine-level aspects in
`src/testing/Test_Dialect.v`, the value-level ones in `src/testing/Test_Dialects.v`
(the same query run under the five dialects, with the expected result in each), and, for
OceanBase MySQL mode, by the conformance with the results which OceanBase records (next
section). `planned` means that it is not modelled yet.

| Aspect | PostgreSQL | MySQL 8 | SQLite | OceanBase MySQL mode | OceanBase Oracle mode | Status |
|---|---|---|---|---|---|---|
| Default `ORDER BY` position of NULL | largest | smallest | smallest | smallest | largest (doc) | done |
| `NULLS FIRST/LAST` in `ORDER BY` | yes | no | yes (3.30) | no (grammar: only in the `ORDER BY` of `ARRAY_AGG`) | yes (doc example) | done |
| Collation of strings | byte-wise | `utf8mb4_0900_ai_ci`: case insensitive, no padding | `BINARY` | `utf8mb4_general_ci` (collation 45): case insensitive, `PAD SPACE` | byte-wise | done (`canon`, `coll_key`) |
| `'a' = 'a '` | false | false | false | true (`'a' LIKE 'a '` is false) | false | done |
| `FULL JOIN` | yes | no | yes (3.39) | yes (grammar) | yes (doc) | done |
| `RIGHT JOIN` | yes | yes | yes (3.39) | yes | yes | done |
| `LATERAL` | yes | yes (8.0.14) | no | yes (grammar; doc, since 4.3.1) | yes (doc, since 4.3.1) | done |
| `INTERSECT`/`EXCEPT` (`MINUS`) | yes | yes (8.0.31) | yes | yes (grammar: `INTERSECT`, `EXCEPT`, `MINUS`) | yes (`UNION [ALL]`, `INTERSECT`, `MINUS`; doc) | done |
| `INTERSECT ALL`/`EXCEPT ALL` | yes | yes (8.0.31) | no | no (syntax error 1064, test suite) | no (doc) | done |
| Window functions | yes | yes | yes (3.25) | yes | yes | done |
| Window frame modes | `ROWS`, `RANGE`, `GROUPS` | `ROWS`, `RANGE` | `ROWS`, `RANGE`, `GROUPS` | `ROWS`, `RANGE` (grammar) | `ROWS`, `RANGE` (doc) | done for `ROWS`, `GROUPS`; `RANGE` with an offset is planned |
| `FILTER` on aggregates | yes | no | yes (3.30) | no (grammar) | no (doc) | done |
| `ANY`/`ALL` subqueries | yes | yes | no | yes | yes | done |
| Conditions are values (booleans) | boolean | integers 1/0 | integers 1/0 | integers 1/0 | no | done (`F_Cond_Value`, `truth_of_value`) |
| String vs. number in a comparison | UNKNOWN (an error in PostgreSQL) | string read as a number | different: numbers < strings | as MySQL | string converted, UNKNOWN if not a number | done |
| Prefix of a string read as a number (`'12abc'`) | no | yes | yes | yes | no: `ORA-01722` | done |
| `/` on integers | integer, truncated | decimal, scale of the dividend + 4, rounded | integer, truncated | as MySQL (but see below) | exact | done |
| Division by zero | error | NULL | NULL | NULL (no `ERROR_FOR_DIVISION_BY_ZERO` by default) | error (`ORA-01476`) | done |
| `mod(x, 0)` | error | NULL | NULL | NULL | `x` (source) | done |
| Invalid cast / string used as a number | error (`invalid input syntax`) | prefix read, warning | prefix read | prefix read | error (`ORA-01722`) | done |
| Scalar subquery with several rows | error | error | value of the first row | error | error | done |
| `\|\|` | concatenation | logical OR | concatenation | logical OR (test suite) | concatenation, NULL is `''` (source) | done |
| `CONCAT` and NULL | ignores NULL | NULL | ignores NULL | NULL (test suite) | `NULL \|\| x` is `x` (source) | done |
| `''` and NULL | different | different | different | different | the same (source: `is_null_oracle`) | done |
| `LIKE` case sensitivity | sensitive | insensitive | insensitive (ASCII) | insensitive | sensitive | done |
| `SUBSTR(s, 0, n)`, negative start | start clipped to 1 | `''` / from the end | position 0 is before the first character | `''` / from the end (test suite) | start 1 / from the end (source) | done |
| `GREATEST`/`LEAST` with a NULL | ignores NULL | NULL | scalar `max`/`min`: NULL | NULL (source) | NULL (source) | done |
| `avg`, `sum` of integers | exact numeric, integer | decimal (scale + 4), integer | real, integer | as MySQL | number | done |
| Aggregate names | `string_agg`, `bool_and` | `group_concat` | `group_concat`, `total` | as MySQL | `listagg` (NULLs ignored; doc) | done |
| Aggregate in `ORDER BY` makes a single group | yes | yes | yes | yes (test suite) | yes | done |
| Default `sql_mode` | n/a | `ONLY_FULL_GROUP_BY`, `STRICT_TRANS_TABLES`, ... | n/a | `STRICT_ALL_TABLES`, `NO_ZERO_IN_DATE`, `NO_AUTO_CREATE_USER` (source) | n/a | recorded |
| Bare columns in a grouped query | rejected | rejected (`ONLY_FULL_GROUP_BY`) | allowed (arbitrary row; the row of the `min`/`max`) | allowed by default (value is implementation defined) | rejected | planned |
| Row limiting | `LIMIT`/`OFFSET`, `FETCH FIRST` | `LIMIT`/`OFFSET` | `LIMIT`/`OFFSET` | `LIMIT`/`OFFSET` | `OFFSET ... FETCH FIRST ... ROWS [ONLY \| WITH TIES]`, `PERCENT` | `LIMIT`/`OFFSET` done; `WITH TIES`, `PERCENT` planned |
| `ROLLUP`, `CUBE`, `GROUPING SETS` | yes | `WITH ROLLUP` | no | yes (grammar) | yes | yes (`GROUPING()` too) |
| `WITH RECURSIVE` | yes | yes | yes | yes (grammar) | yes | yes (bounded by `rec_fuel`) |
| Functions, predicates and aggregates which exist only in some dialects (`string_agg`, `group_concat`, `listagg`, `total`, `ifnull`, `nvl`, `is distinct from`, `<=>`) | | | | | | done (`accepted_by` checks the names) |
| Integer range and overflow | 4/8 bytes, error | 8 bytes, error | 8 bytes, to real | as MySQL | number | not modelled |
| Floating-point numbers | `float8`/`float4`, errors on overflow, underflow and division by zero, NaN = NaN and greatest; shortest text, `1e+15` | `DOUBLE`, `FLOAT` (binary32); strings in arithmetic are doubles; overflow is an error; shortest text, `1e15` | `REAL` (binary64); text `%!.15g` (`0.3`, `1.0e+15`) | as MySQL | `NUMBER` (no float literal) | done (`IEEE.v`, `Value_F`: correctly rounded operations, binary64 and binary32) |
| Accent folding (`_ai_ci`) | no | yes | no | yes | no | not modelled |
| Blobs, dates, JSON, regular expressions | | | | | | not modelled |

## The MySQL family: MariaDB, TiDB, Percona, PolarDB

These four share the value semantics of `MySQL.v` (`mysql_vs`, parameterised by the padding and the
case sensitivity of the collation, and by the constructs supported). The differences which the
formal model captures, from the source of MariaDB and TiDB (`MariaDB/server` at `39281811`,
`pingcap/tidb` at `e35413c`, November 2026) and from the documentation of PolarDB and Percona:

| | MySQL 8 | MariaDB | TiDB | Percona Server | PolarDB (MySQL edition, 8.0.2) |
|---|---|---|---|---|---|
| Default collation | `utf8mb4_0900_ai_ci`, NO PAD | `utf8mb4_uca1400_ai_ci`, PAD SPACE | `utf8mb4_bin`, PAD SPACE: case sensitive | as MySQL | as MySQL |
| `ONLY_FULL_GROUP_BY` by default | yes | no | yes | yes | yes |
| `INTERSECT`, `EXCEPT` (with `ALL`) | yes (8.0.31) | yes | yes | yes | no (MySQL 8.0.18) |
| `FULL JOIN` | no | no | yes (`FULL OUTER JOIN`) | no | no |
| `LATERAL` | yes | no | yes | yes | yes |
| `FILTER (WHERE ...)` | no | yes | no | no | no |
| `FETCH FIRST ... WITH TIES` | no | yes | no | no | no |
| `GROUPS` frames | no | no | parsed, rejected by the planner | no | no |
| `ROLLUP`, `CUBE`, `GROUPING SETS` | `WITH ROLLUP` | `WITH ROLLUP` | `WITH ROLLUP`, `GROUPING()` | `WITH ROLLUP` | `WITH ROLLUP` |
| `NULLS FIRST/LAST` | no | no | no | no | no |

Not covered for these systems: the Oracle mode of MariaDB (`sql_mode=ORACLE`), the functions which exist in
only one of them (the tables are those of MySQL), TiDB's new-collation framework beyond `utf8mb4_bin`,
the value of a bare column in MariaDB, and the optimizer-visible differences (which do not change results).
Percona's source and the PolarDB engine are not open for the SQL layer in the same way: for these two the model
relies on the documentation (`docs.percona.com` could not be fetched; the feature comparison was read through a mirror).

## Versions (TODO 4.10)

`src/data/dialects/Versions.v` gives the release which introduced each construct (`introduced`), per family
(PostgreSQL, MySQL, SQLite, MariaDB, TiDB), and `at_version d fam v` restricts a dialect to the constructs of
version `v` (`at_version_sub`: a version never extends a dialect). Named versions: `MySQL57`, `MySQL80` (8.0.30),
`MySQL84`, `PostgreSQL12`, `PostgreSQL17`, `SQLite3_24`, `SQLite3_45`, `MariaDB10_4`, `MariaDB10_6`, `TiDB4`.
Only the acceptance of constructs depends on the version; the values of functions are those of the latest
version (a function added in a release is accepted by earlier ones). Tests: `src/testing/Test_Versions.v`.

## OceanBase Oracle mode (closeout, TODO 4.9)

The parser of the Oracle mode (`sql_parser_oracle_mode.y`) is in the closed enterprise source of OceanBase, and
no expected results are recorded for it. Every behaviour of the model is therefore taken either from the **shared
engine source** (`src/sql/engine/expr/`, which both modes run: marked *source*) or from the **Oracle-mode SQL
reference** of `oceanbase-doc` (marked *doc*). Nothing is taken from Oracle Database itself without saying so.

| Construct | Model | From |
|---|---|---|
| `''` is NULL; `\|\|` with NULL as `''`; `CONCAT` | `ora_isnull`, `ora_concat` in `OceanBase.v` | source (`is_null_oracle`, `ob_expr_concat.cpp`) |
| `DECODE`, `NVL`, `NVL2`, `MINUS` | functions `decode`, `nvl`, `nvl2`; `SQ_Set Except` | doc; `decode` NULL = NULL is true (doc) |
| Division by zero, `MOD(x, 0)`, invalid number | `ORA-01476` error, `x`, `ORA-01722` error | source |
| Date arithmetic (`date ± n`, `date - date`) | `ora_date_arith`: days as numbers | source, doc |
| `TO_CHAR`, `TO_DATE`, `TO_NUMBER` | the datetime format elements (`YYYY`, `RR`, `MON`, `MM`, `DD`, `HH24`, `MI`, `SS`, ...; default `DD-MON-RR`); `TO_CHAR` of a number ignores the format model; `TO_NUMBER` converts strictly, and drops the `,` and `$` of a format model | doc |
| `LISTAGG ... WITHIN GROUP` | `listagg`, `listagg_sep` (NULLs ignored) | doc |
| `DUAL` | a one-row table, as in the MySQL mode | doc |
| `CONNECT BY`, `START WITH`, `PRIOR`, `LEVEL` | derived form `connect_by` (`SqlFullSyntax.v`): a recursive CTE whose anchor is the `START WITH` rows at level 1 and whose recursive step joins a row whose `PRIOR` columns match; `test Test_OracleForms.hierarchy` | doc |
| `ROWNUM <= n` | derived form `rownum_le`: `LIMIT n` with no order (any `n` rows: `limit_any` in the runner) | doc |
| `PIVOT (agg (v) FOR k IN (k1 AS a1, ...))` | derived form `pivot`: `agg (CASE WHEN k = ki THEN v END)` grouped by the other columns | doc |
| `UNPIVOT (v FOR k IN (c1 AS 'k1', ...))` | derived form `unpivot`: a `UNION ALL` of one `SELECT` per column, `WHERE ci IS NOT NULL` (the default `EXCLUDE NULLS`) | doc |
| `OFFSET ... FETCH FIRST ... ROWS ONLY \| WITH TIES` | `order_limit` and the ties of `F_Fetch_Ties` | doc |
| `LATERAL`, `CROSS APPLY`, `OUTER APPLY` | `Fr_Join` with `lateral` | doc (since 4.3.1) |
| Analytic functions, `ROWS`/`RANGE` frames | the windows of `SqlFull.v` | doc |
| `ROLLUP`, `CUBE`, `GROUPING SETS`, `GROUPING()` | the grouping sets of `SqlFull.v` | doc |

Excluded, with the reason:

- `(+)` outer-join markers: an older notation of `LEFT`/`RIGHT JOIN`, which the translator would rewrite; a
  `WHERE` with `(+)` on both sides of an `OR` is rejected by the engine, a rule the model does not need.
- `ROWID`: a physical address; its value is not determined by the query.
- `SAMPLE`: random (the result is any sub-bag of the rows, like `TABLESAMPLE`): not a function of the database.
- `MODEL` clause: not supported by OceanBase (absent from the Oracle-mode SQL reference).
- `KEEP (DENSE_RANK FIRST ORDER BY k)`: expressible as the aggregate over the rows whose `k` is the minimum of
  the group (a correlated subquery); not a separate construct of the model.
- `CONNECT BY NOCYCLE`, `CONNECT_BY_ROOT`, `SYS_CONNECT_BY_PATH`, `ORDER SIBLINGS BY`: not modelled. A cyclic
  hierarchy without `NOCYCLE` is an error (`ORA-01436`); the model stops at `rec_fuel` instead.

## Sources and how they were checked

For PostgreSQL, the manual. For MySQL, the 8.0/8.4 reference manual
([SQL modes](https://dev.mysql.com/doc/refman/8.0/en/sql-mode.html): in a `SELECT`,
division by zero is NULL). For SQLite,
[Datatypes In SQLite](https://www.sqlite.org/datatype3.html) (the order of storage classes,
affinity and its role in comparisons).

**OceanBase** is open source, and its behaviour is established from its code, not from
guesses. Two repositories were read:
[`oceanbase/oceanbase`](https://github.com/oceanbase/oceanbase) at `d375c6d` (11 November 2026) and
[`oceanbase/oceanbase-doc`](https://github.com/oceanbase/oceanbase-doc) at `2a5ae3a` (19 December 2025).
The online documentation site is not reachable from the development environment, so the
Markdown sources of the documentation were read instead.

- *Grammar of the MySQL mode*, `src/sql/parser/sql_parser_mysql_mode.y`: `set_type` has
  `UNION [ALL | DISTINCT]`, `INTERSECT`, `EXCEPT`, `MINUS` and no `ALL` for the last three;
  `LATERAL table_subquery`; `FULL [OUTER] JOIN`; `win_rows_or_range` is `ROWS | RANGE` (there is
  no `GROUPS`); there is no `FILTER (WHERE ...)`; `NULLS FIRST/LAST` is only in
  `order_by_opt_null`, used by `ARRAY_AGG`; `ROLLUP`, `CUBE`, `GROUPING SETS`, `WITH RECURSIVE`.
- *Defaults*: `src/share/system_variable/ob_system_variable_init.json` gives `collation_server`
  45, that is `utf8mb4_general_ci` (`CS_TYPE_UTF8MB4_GENERAL_CI = 45` in `ob_charset.h`), and
  `sql_mode` 281018368, which `deps/oblib/src/common/sql_mode/ob_sql_mode.h` decodes as
  `STRICT_ALL_TABLES | NO_ZERO_IN_DATE | NO_AUTO_CREATE_USER`: neither `ONLY_FULL_GROUP_BY` nor
  `PIPES_AS_CONCAT` nor `ERROR_FOR_DIVISION_BY_ZERO`.
- *Engine (shared by the two modes)*, `src/sql/engine/expr/`: `ObObj::is_null_oracle`
  (`deps/oblib/src/common/object/ob_object.h`: NULL, or a character value of length 0);
  `ob_expr_concat.cpp` (in Oracle mode a NULL operand is an empty string, and the result is NULL
  only if both are); `ob_expr_mod.cpp` (`MOD(x, 0)` is `x` in Oracle mode, NULL in MySQL mode);
  `ob_expr_div.cpp` (division by zero is an error in Oracle mode); `ob_expr_least.cpp`
  (`calc_mysql` and `calc_oracle` both return NULL as soon as an argument is NULL);
  `ob_expr_substr.cpp` (in Oracle mode a start of 0 is 1).
- *Expected results*, `tools/deploy/mysql_test` (433 result files recorded from OceanBase in
  MySQL mode): see the conformance section below.
- *Documentation* (`oceanbase-doc`, `en-US/700.reference/500.sql-reference`), for the Oracle
  mode: set operators (`UNION [ALL] | MINUS | INTERSECT`), `OFFSET ... FETCH`, `LISTAGG`,
  windowing clause `{ROWS | RANGE}`, `LATERAL` derived tables (release 4.3.1), an
  `ORDER BY ... NULLS LAST` example, NULLs sort last in ascending order.

**The parser of the Oracle mode is not in the open-source repository** (nor are expected
results for the Oracle mode). What is said about the Oracle mode therefore rests on its
documentation, and on the code of the engine, which the two modes share. Two Oracle-mode
points are taken from Oracle, and not checked: `LIKE` has no default escape character, and
`GROUPS` frames, `FILTER` and `INTERSECT ALL` are rejected (they are absent from the grammar
in the documentation).

## Conformance with the results recorded by OceanBase (MySQL mode)

`tools/spec/sql2coq.py` replays the statements of the test scripts of OceanBase together with
the results which OceanBase recorded, translates the `SELECT` statements which are in the
fragment of `SqlFull.v` to Coq, and `tools/spec/run.sh` checks that the formal semantics of a
dialect gives the same results. A statement which is not in the fragment is skipped, and the
tables which it modifies are marked unreliable, so that a skipped statement never makes a case
wrong. A script whose data come from a loop, a procedure or a transaction is skipped as a
whole, because the statements which its loop runs are not in the result file.

```
tools/spec/run.sh /path/to/oceanbase OceanBaseMySQL
```

The generated Coq files contain data from the test suite of OceanBase: they are written to
`src/testing/spec/`, which is not tracked.

## What the value-level models do not do

- Integers are unbounded and non-integer numbers are exact rationals: overflows, the
  ranges of the types and floating-point rounding are not modelled.
- SQLite affinity: the conversions which SQLite applies when a column is compared with
  a literal are not modelled (a literal is compared with a column as with any value).
- Runtime errors (a division by zero in PostgreSQL, an invalid conversion in Oracle) are
  NULL, as everywhere in this development (open issue I3).
- A function which a dialect does not have is NULL, and a predicate which it does not
  have is UNKNOWN; the acceptance check does not look at names yet.

## Plan

1. (done) The engine-level framework (`dialect`) and its tests.
2. (done) The value-level dialects: PostgreSQL, MySQL, SQLite, OceanBase (two modes), with
   the same query run under each (`vsem`, `TD`, `to_dialect`).
3. The acceptance rules: functions and aggregates by name, `ONLY_FULL_GROUP_BY`, and the
   semantics of bare columns (SQLite).
4. More of each dialect: dates and times, the rest of the string and numeric functions,
   regular expressions.
5. Floating-point numbers (IEEE 754) where the dialect has them.
