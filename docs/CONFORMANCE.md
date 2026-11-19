# Conformance of the formal semantics with real database engines

The semantics of the dialects (`docs/DIALECTS.md`) is not only argued from documentation: it
is checked against the results which real engines record. Two sources are used.

| Source | What it is | Used for | License |
|---|---|---|---|
| [OceanBase `mysql_test`](https://github.com/oceanbase/oceanbase/tree/master/tools/deploy/mysql_test) | 433 result files, recorded from OceanBase in MySQL mode | OceanBase (MySQL mode) | MulanPubL-2.0: not copied into this repository |
| [sqllogictest](https://github.com/gregrahn/sqllogictest) | millions of queries whose results were computed by SQLite, MySQL, PostgreSQL, Oracle and SQL Server, and which says where they differ (`skipif mysql`, `onlyif sqlite`) | SQLite, PostgreSQL, MySQL, OceanBase (MySQL mode) | CC0 / MIT / BSD: a sample is copied into `src/testing/slt/` |

## How

A script translates the `SELECT` statements which are in the fragment of `SqlFull.v` to Coq;
the Coq side builds the database of the script, runs the query in the formal semantics of a
dialect, and compares the rows with the recorded ones. A statement which is not in the
fragment (a function the model does not have, an unsupported type, a construct which is not
formalised) is **skipped**, never approximated; a table modified by a skipped statement is
marked unreliable, and the queries which read it are skipped as well. So a failure is a
disagreement between the model and the engine, not an artefact of the translation, and a
success is a query whose result the model reproduces.

- `tools/spec/sql2coq.py`, `tools/spec/run.sh`, `src/testing/SpecRunner.v`: the test suite of
  OceanBase. The script of the test (`t/*.test`) is replayed in full, so that the statements
  which the result file does not echo (`--disable_query_log`) are applied; the echoed
  statements give the recorded results. A script which loops (`while`, `eval`), uses several
  connections, procedures or transactions is skipped as a whole. Queries which depend on an
  implementation-defined choice are skipped: a column which is neither grouped nor in an
  aggregate, `LIMIT` without `ORDER BY`, the order of the elements of `group_concat`.
- `tools/spec/slt2coq.py`, `tools/spec/run_slt.sh`, `src/testing/SltRunner.v`: sqllogictest.
  The directives select the queries which apply to an engine, results are converted as
  sqllogictest does (`I` integer, `R` `%.3f`, `T` text, `(empty)`, `NULL`), results which are
  only given by their hash are skipped.

```
tools/spec/run.sh     /path/to/oceanbase OceanBaseMySQL
tools/spec/run_slt.sh /path/to/sqllogictest mysql OceanBaseMySQL 300 /path/to/test/random/expr/slt_good_0.test
```

Both tools discriminate: the same cases run under another dialect fail (for instance 21 of the
71 first OceanBase cases fail under PostgreSQL, and the queries of SQLite fail under MySQL
because of the integer division).

## Results

**OceanBase, MySQL mode** (`OceanBaseMySQL`): 769 queries are translated and replayed. Dates, times
and `datetime(6)` columns are translated since TODO 1.5. String functions, bit operators, `LIKE ... ESCAPE`
and the standard syntaxes `TRIM(... FROM ...)`, `POSITION`, `SUBSTRING ... FROM` are translated since TODO
2.1–2.3.

Run 16 is the latest, made after TODO 3.9–3.11. Since then the runner checks a query whose order is not fully determined
against the groups of rows with equal sort keys (`ties_ok`), and a `LIMIT` without `ORDER BY` as any sub-bag of
the right size (`limit_any`). The translator also reads aliases in `HAVING` and `ORDER BY`, locking clauses
(`FOR UPDATE`, `LOCK IN SHARE MODE`: no effect on the rows), and a single-column result whose only row is
`''`. In that run **768** queries gave the recorded result: every query except the time-limit case below.

- `rqg_subquery_semijoin_nested_timeout` (one query) exceeds the time limit of the runner (`FILE_TIMEOUT`,
  900 s): the tuples of the model are lists, so a row of many columns is slow to build.
  `join_many_table` (32 left joins) passes since the labels of a joined row are computed once
  (`join_tuple`) and the rows of a join are checked for errors only when an operand holds a failed row.

Two deviations of the model were found by run 16 and fixed. `SUBSTRING_INDEX` with a negative count searches
for the delimiter from the right, which differs when the occurrences overlap
(`substring_index('aaaaaaaaa1', 'aa', -1)` is `'1'`). And a count of `9223372036854775807` no longer builds a
unary number (the counts are bounded by the number of pieces).

Run 15 (749/752) left the two tie orders of `expr_floor:56` and `expr_floor:57` (`ORDER BY floor(i4)`).
They pass with `ties_ok`: the order of rows with equal sort keys is not specified by SQL.

The queries on a table whose rows a foreign key may change by a cascade (`ON DELETE CASCADE`, `SET NULL`)
after a statement on its parent are not translated: the translator does not replay the cascades.

Earlier milestones: 570/570 after the decimal scale (TODO 1.2.1: `length(0.00)`, `4/3 = 1.333333333`)
and binary floating point (TODO 1.2.2: the `sum` of a `FLOAT` column is `147.57999897003174`).

Since TODO 1.2.1, a decimal of the model has a scale, and is compared with the recorded text exactly
(`1.3333`, `0.00`): the former deviations `length(0.00)` and `4/3 = 1.333333333` are gone. The latter was
not a deviation of OceanBase: MySQL's decimal library holds quotients by units of 9 digits.

Since TODO 1.1, a query on which the model fails is printed `ERROR`, so a failure of the model can never
pass for a NULL; no query of the suite fails in the model.

**PostgreSQL regression tests** (`PostgreSQL`, TODO 5.3): `tools/spec/pg_run.sh POSTGRES_CHECKOUT` converts the
expected output of `src/test/regress` (`expected/*.out`, the psql tables) with `tools/spec/pg2result.py`, translates it
with `sql2coq.py --dialect PostgreSQL --lenient`, and checks it. The tables of `test_setup.sql` are loaded first (their
`COPY` files become `INSERT`s; `tenk1` and `tenk2`, of 10,000 rows, are left out). A result is not checked when it cannot
be read without ambiguity: an empty cell (NULL and `''` print the same), a cell on several lines, a date printed after the
test changed `DateStyle`, a time zone, a BC date or an interval in the `postgres` style. In `--lenient` mode a transaction
block, a routine, a data-modifying `WITH` or an inheritance child makes the tables it mentions unreliable, instead of
skipping the file.

Run 1 (`postgres/postgres` at `b443bc7`; `select`, `aggregates`, `window`, `with`, `join`, `subselect`, `union`,
`numeric`, `text`, `float8`, `date`, `timestamp`, `json`, `arrays`, `groupingsets`; `strings` and `jsonb` change the psql
display and are skipped): **320** queries translated, **232** pass. The 88 failures:

| Count | Reason | Status |
|---|---|---|
| 30 | `NaN`, `Infinity` of `float8` and `numeric`; `infinity` dates and timestamps | not representable: `Value_F` and `Value_D` are finite, dates are days (open) |
| 17 | `format` with a width (`%10s`, `%-10s`, `%*s`, `%1$10s`) | not modelled yet (`pg_format` has the conversions without widths) |
| 14 | `json_strip_nulls` | not modelled yet |
| 12 | BC and AD dates (`DATE '0001-12-31 BC'`) | the date parser reads only years of the common era (open) |
| 8 | `x = ANY ('{1,2,3}')`: a string literal read as an array of the type of `x` | not modelled yet (an array value is modelled; the literal of type `unknown` is not converted) |
| 2 | `concat` of a date: the date in `DateStyle` `Postgres, MDY` | the model prints ISO dates (the regression database's `DateStyle` is not modelled) |
| 1 | `rank('3') WITHIN GROUP (ORDER BY x)`: `'3'` takes the type of `x` | same as the arrays: the type of an `unknown` literal |
| 1 | `EXTRACT(JULIAN FROM ...)` | not modelled yet |
| 1 | `0 ^ 0.5` on `numeric` | `power` of `numeric` is exact for integer exponents only |
| 1 | `' true '::json` | the runner reads psql's cells without their padding: not a deviation |
| 1 | `json_array_elements` with nested objects | the cells of nested JSON (psql pads them) |

Fixed by this run (they were deviations of the model): `text || integer` converts the integer (`'four: ' || 2+2`), a
boolean is `t`/`f` in `concat`, a date compared with a string literal reads the literal as a date, a timestamp prints the
fewest fractional digits (`date_trunc` gave `.000000`), and `json` keeps its input text. In the translator: `::` casts,
`FILTER (WHERE ...)`, the precedence of `||` below `+`, `TRUE`/`FALSE` as booleans.

**sqllogictest** (queries are selected for an engine by the directives):

| Scripts | SQLite | PostgreSQL | MySQL | OceanBase (MySQL mode) |
|---|---|---|---|---|
| `test/evidence` (language reference of SQLite, with the cases where engines differ) | 128 | 88 | 88 | 88 |
| `test/random/expr` (arithmetic, comparison, `CASE`, `BETWEEN`, `IN`, `COALESCE`, `NULLIF`, `CAST`, aggregates; integer division written `/` or `DIV` according to the engine): 24 scripts, 400 queries each | 9600 | 9600 | 9600 | 9600 |
| `test/random/select`, `random/aggregates`, `random/groupby`, `index/between`, `index/in`, `index/orderby`: 15 scripts, 300 queries each (joins, subqueries, `GROUP BY`, `HAVING`, `ORDER BY`, set operations) | 7200 | 7200 | 7200 | not run |

**0 failures** in each cell. (Queries whose result is only given by its MD5 hash, and the
`bare column` queries whose value is implementation defined, are not counted.)

A sample, 150 queries of `test/evidence` and of 6 scripts of `random/expr` for each dialect, is
copied into `src/testing/slt/` and checked as part of the build (37 files): a change of the
semantics which breaks the behaviour of an engine breaks the build.

The Oracle mode is not run against sqllogictest: the expected results were produced by SQLite,
MySQL and PostgreSQL, the scripts have no `skipif oracle`, and the Oracle division `/` is exact
(`61 / 88 * 96` is 0 in the recorded results, 66.5 in Oracle). The Oracle mode is checked
against the documentation and the source of the engine instead (`docs/DIALECTS.md`).

## What this found

The conformance runs found, and fixed, defects which the examples written by hand had not:

- the quotient of decimals and `avg` are rounded to the scale of the dividend plus
  `div_precision_increment` (`4/3` is `1.3333`, `avg(1,2,5)` is `2.6667`);
- an aggregate belongs to the innermost block which binds a column of its argument, also when
  the column is read by a subquery in the argument (`sum((select sum(c1) from t1))` aggregates the
  rows of the outer block);
- an aggregate in `ORDER BY` makes the query an aggregate query with a single group
  (`SELECT 1 FROM t ORDER BY avg(a)` returns one row);
- the text of a decimal (`length(12.466)`), and `LOCATE` with a start position;
- OceanBase has `LATERAL` and no `INTERSECT ALL`; its default collation pads with spaces
  (`'a' = 'a '`) and its default `sql_mode` has neither `ONLY_FULL_GROUP_BY` nor
  `PIPES_AS_CONCAT`, so `||` is the logical OR (all of this from its source, see
  `docs/DIALECTS.md`);
- in the translator: scripts whose data come from statements which are not echoed, `zerofill`,
  column collations, integer ranges and string lengths, aliases in `ORDER BY` and `GROUP BY`.

## Not covered

Floating-point rounding (reals are exact rationals), the scale of decimals, dates and times,
window functions and `WITH` in the translator (the semantics has them, but no recorded
result file is translated yet), regular expressions, and everything which reads or modifies
data through `UPDATE`, `DELETE`, `INSERT ... SELECT` (other than a copy `SELECT *`).
