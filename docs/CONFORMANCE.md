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

**OceanBase, MySQL mode** (`OceanBaseMySQL`): 638 queries are translated and replayed (dates, times and
`datetime(6)` columns are translated since TODO 1.5), and **635** give the recorded result:

- `expr_floor:56` and `expr_floor:57` (`ORDER BY floor(i4)`) list the rows with equal keys in another order:
  the order of rows with equal sort keys is not specified by SQL, and the model keeps the order of the
  table where OceanBase keeps the order of its plan. Not a deviation of the semantics.
- `rqg_subquery_semijoin_nested_timeout` (one query) exceeds the time limit of the runner (`FILE_TIMEOUT`,
  900 s): the tuples of the model are lists, so a row of many columns is slow to build.
  `join_many_table` (32 left joins) passes since the labels of a joined row are computed once
  (`join_tuple`) and the rows of a join are checked for errors only when an operand holds a failed row.

The queries on a table whose rows a foreign key may change by a cascade (`ON DELETE CASCADE`, `SET NULL`)
after a statement on its parent are not translated: the translator does not replay the cascades.

Earlier milestones: 570/570 after the decimal scale (TODO 1.2.1: `length(0.00)`, `4/3 = 1.333333333`)
and binary floating point (TODO 1.2.2: the `sum` of a `FLOAT` column is `147.57999897003174`).

Since TODO 1.2.1, a decimal of the model has a scale, and is compared with the recorded text exactly
(`1.3333`, `0.00`): the former deviations `length(0.00)` and `4/3 = 1.333333333` are gone. The latter was
not a deviation of OceanBase: MySQL's decimal library holds quotients by units of 9 digits.

Since TODO 1.1, a query on which the model fails is printed `ERROR`, so a failure of the model can never
pass for a NULL; no query of the suite fails in the model.

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
