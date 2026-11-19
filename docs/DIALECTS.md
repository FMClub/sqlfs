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

`done` means that it is modelled and tested: the engine-level aspects in
`src/testing/Test_Dialect.v`, the value-level ones in `src/testing/Test_Dialects.v`
(the same query run under the five dialects, with the expected result in each).
`planned` means that it is not modelled yet.

| Aspect | PostgreSQL | MySQL 8 | SQLite | OceanBase MySQL mode | OceanBase Oracle mode | Status |
|---|---|---|---|---|---|---|
| Default `ORDER BY` position of NULL | largest | smallest | smallest | smallest | largest | done |
| `NULLS FIRST/LAST` | yes | no | yes (3.30) | no | yes (assumed) | done |
| Case-insensitive grouping, `DISTINCT`, set operations | no | yes (`utf8mb4_0900_ai_ci`) | no (`BINARY`) | yes | no | done (`canon`) |
| `FULL JOIN` | yes | no | yes (3.39) | yes (documented) | yes | done |
| `RIGHT JOIN` | yes | yes | yes (3.39) | yes | yes | done |
| `LATERAL` | yes | yes (8.0.14) | no | no (assumed) | no (assumed) | done |
| `INTERSECT`/`EXCEPT` | yes | yes (8.0.31) | yes | yes (documented) | yes (`MINUS`) | done |
| `INTERSECT ALL`/`EXCEPT ALL` | yes | yes (8.0.31) | no | no (assumed) | no | done |
| Window functions | yes | yes | yes (3.25) | yes | yes | done |
| `GROUPS` frames | yes | no | yes | no (assumed) | no | done |
| `FILTER` on aggregates | yes | no | yes (3.30) | no | no | done |
| `ANY`/`ALL` subqueries | yes | yes | no | yes | yes | done |
| Conditions are values (booleans) | boolean | integers 1/0 | integers 1/0 | integers 1/0 | no | done (`F_Cond_Value`, `truth_of_value`) |
| String vs. number in a comparison | UNKNOWN (an error in PostgreSQL) | string read as a number | different: numbers < strings | as MySQL | string converted, UNKNOWN if not a number | done |
| Prefix of a string read as a number (`'12abc'`) | no | yes | yes | yes | no (error) | done |
| Comparison of strings | byte-wise | case insensitive | byte-wise | case insensitive | byte-wise | done |
| `/` on integers | integer, truncated | exact | integer, truncated | exact | exact | done |
| Division by zero | error (NULL here) | NULL | NULL | NULL | error (NULL here) | done |
| `mod(x, 0)` | error (NULL here) | NULL | NULL | NULL | `x` | done |
| `\|\|` | concatenation | logical OR | concatenation | logical OR | concatenation, NULL is `''` | done |
| `CONCAT` and NULL | ignores NULL | NULL | ignores NULL | NULL | ignores NULL | done |
| `''` and NULL | different | different | different | different | the same | done |
| `LIKE` case sensitivity | sensitive | insensitive | insensitive (ASCII) | insensitive | sensitive | done |
| `SUBSTR(s, 0, n)`, negative start | start clipped to 1 / from position 1 | `''` / from the end | position 0 is before the first character / from the end | as MySQL | start 1 / from the end | done |
| `GREATEST`/`LEAST` with a NULL | ignores NULL | NULL | scalar `max`/`min`: NULL | NULL | NULL | done |
| `avg`, `sum` of integers | exact numeric, integer | exact | real, integer | as MySQL | number | done (as exact numbers) |
| Aggregate names | `string_agg`, `bool_and` | `group_concat` | `group_concat`, `total` | as MySQL | `listagg` | done |
| `typeof`, storage classes | no | no | yes | no | no | partly (`typeof`) |
| Bare columns in a grouped query | rejected | rejected (`ONLY_FULL_GROUP_BY`) | allowed (arbitrary row; the row of the `min`/`max`) | rejected | rejected | planned |
| Names of functions which exist only in some dialects | | | | | | planned (acceptance by name) |
| Integer range and overflow | 4/8 bytes, error | 8 bytes, error | 8 bytes, to real | as MySQL | number | not modelled |
| Floating-point numbers | IEEE | IEEE | IEEE | IEEE | binary float | not modelled (exact rationals) |
| Accent folding (`_ai_ci`) | no | yes | no | yes | no | not modelled |
| Blobs, dates, JSON, regular expressions | | | | | | not modelled |

Sources used: the PostgreSQL manual; for MySQL the 8.0/8.4 reference manual
([SQL modes](https://dev.mysql.com/doc/refman/8.0/en/sql-mode.html): in a `SELECT`,
division by zero is NULL); for SQLite
[Datatypes In SQLite](https://www.sqlite.org/datatype3.html) (the order of storage
classes, affinity and its role in comparisons). For OceanBase:
the [compatibility with MySQL](https://en.oceanbase.com/docs/common-oceanbase-database-10000000001228196)
page (set operations, `FULL JOIN`), the
[SIMPLE SELECT](https://en.oceanbase.com/docs/common-oceanbase-database-10000000001171133)
reference (`FULL [OUTER] JOIN`, `FETCH FIRST`), and
[LISTAGG](https://en.oceanbase.com/docs/common-oceanbase-database-10000000001032476)
(NULLs are ignored). The documentation does not state every point: the entries marked
"assumed" (`LATERAL`, the `ALL` forms of `INTERSECT` and `EXCEPT`, `GROUPS` frames, and
`NULLS FIRST/LAST` in Oracle mode) are conservative assumptions, to be checked against a
tenant of each mode. The empty string being NULL and the other Oracle-mode behaviours
are taken from Oracle.

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
