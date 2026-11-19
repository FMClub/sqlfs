# SQL dialects

The goal is one formal semantics of the query language of SQL which covers the
mainstream relational systems: PostgreSQL, MySQL, SQLite and OceanBase (in its
MySQL and Oracle modes). They agree on the structure of queries and on
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

`done` means that it is in the framework and tested (`src/testing/Test_Dialect.v`);
`planned` means that the table below is the plan.

| Aspect | PostgreSQL | MySQL 8 | SQLite | OceanBase MySQL mode | OceanBase Oracle mode | Status |
|---|---|---|---|---|---|---|
| Default `ORDER BY` position of NULL | largest | smallest | smallest | smallest (to verify) | largest | done |
| `NULLS FIRST/LAST` | yes | no | yes (3.30) | no (to verify) | yes | done |
| Case-insensitive grouping, `DISTINCT`, set operations | no (default collation) | yes (default collation `utf8mb4_0900_ai_ci`) | no (`BINARY`) | yes | no | done (`canon`) |
| `FULL JOIN` | yes | no | yes (3.39) | to verify | yes | done |
| `RIGHT JOIN` | yes | yes | yes (3.39) | yes | yes | done |
| `LATERAL` | yes | yes (8.0.14) | no | to verify | yes | done |
| `INTERSECT`/`EXCEPT` | yes | yes (8.0.31) | yes | to verify | yes (`MINUS`) | done |
| `INTERSECT ALL`/`EXCEPT ALL` | yes | yes (8.0.31) | no | to verify | no | done |
| Window functions | yes | yes | yes (3.25) | yes | yes | done |
| `GROUPS` frames | yes | no | yes | to verify | no | done |
| `FILTER` on aggregates | yes | no | yes (3.30) | no | no | done |
| `ANY`/`ALL` subqueries | yes | yes | no | yes | yes | done |
| Conditions are booleans | yes | integers 0/1 | integers 0/1 | integers 0/1 | not first-class | planned |
| Implicit string/number conversion in comparisons | no (error) | yes | by affinity | yes (differs from MySQL by mode, to verify) | yes | planned |
| Cross-type order (`NULL < number < text < blob`) | n/a | n/a | yes | n/a | n/a | planned |
| Comparison of strings | byte-wise / collation | collation, `PAD SPACE` | `BINARY`/`NOCASE`/`RTRIM` | as MySQL | byte-wise | planned |
| `/` on integers | integer, truncated | exact decimal (`DIV` is the integer division) | integer, truncated | as MySQL | exact number | planned |
| Division by zero | error | NULL in `SELECT` | NULL | as MySQL | error | planned |
| `\|\|` | concatenation | logical OR (unless `PIPES_AS_CONCAT`) | concatenation | as MySQL | concatenation | planned |
| `CONCAT` and NULL | ignores NULL | NULL | ignores NULL (3.44) | as MySQL | ignores NULL | planned |
| `''` and NULL | different | different | different | different | the same | planned |
| `LIKE` case sensitivity | sensitive | by collation (insensitive) | insensitive for ASCII | insensitive | sensitive | planned |
| Bare columns in a grouped query | rejected | rejected (`ONLY_FULL_GROUP_BY`) | allowed (value of an arbitrary row) | rejected | rejected | planned |
| `avg` / `sum` result types | numeric / numeric | decimal / decimal | real / integer or real | as MySQL | number | planned |
| Aggregate names | `string_agg`, `bool_and` | `group_concat` | `group_concat`, `total` | as MySQL | `listagg` | planned |
| Integer range and overflow | 4/8 bytes, error | 8 bytes, error | 8 bytes, to real | as MySQL | number | planned |

Sources used: the PostgreSQL manual; for MySQL the 8.0/8.4 reference manual
([SQL modes](https://dev.mysql.com/doc/refman/8.0/en/sql-mode.html): in a `SELECT`,
division by zero is NULL); for SQLite
[Datatypes In SQLite](https://www.sqlite.org/datatype3.html) (the order of storage
classes, affinity and its role in comparisons). For OceanBase the documentation
does not make every point explicit, so the entries marked "to verify" are
assumptions taken from the MySQL or the Oracle behaviour; they are to be checked
against a tenant of each mode.

## Plan

1. (done) The engine-level framework and its tests.
2. Value-level dialects: `PostgreSQL`, `MySQL`, `SQLite`, `OceanBase` (two modes),
   each with its predicates, functions, aggregates and implicit conversions.
3. The remaining acceptance rules: `ONLY_FULL_GROUP_BY` and the semantics of bare
   columns, per dialect.
4. Differential tests: the same query run under every dialect, with the results
   documented.
5. Floating-point numbers (IEEE 754) where the dialect has them (`REAL`, `DOUBLE`).
