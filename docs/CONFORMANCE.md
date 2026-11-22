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

- `tools/spec/compile_spec.sh`, `tools/spec/split_cases.py`: a file of cases is compiled as one
  `vm_compute`, so one slow case used to lose the results of the whole file. A file over `FILE_TIMEOUT`
  is reported as `SPLIT` and compiled again one case at a time, each within `CASE_TIMEOUT` seconds
  (default 120; a case over it is reported as `TIMEOUT_CASE id`). `pg_run.sh` and `suite_run.sh` do this;
  `run.sh` (OceanBase) keeps `CASE_TIMEOUT=0`, which reports the whole file as `TIMEOUT`, unless it is set.

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

Run 20 (after TODO 5.6: mathematical functions, `DATE_ADD` and composite interval units in the translator): **774** translated, **773** pass, the remaining one being the time-limit case below.

Run 16 is the latest, made after TODO 3.9–3.11. Since then the runner checks a query whose order is not fully determined
against the groups of rows with equal sort keys (`ties_ok`), and a `LIMIT` without `ORDER BY` as any sub-bag of
the right size (`limit_any`). The translator also reads aliases in `HAVING` and `ORDER BY`, locking clauses
(`FOR UPDATE`, `LOCK IN SHARE MODE`: no effect on the rows), and a single-column result whose only row is
`''`. In that run **768** queries gave the recorded result: every query except the time-limit case below.

- `rqg_subquery_semijoin_nested_timeout` (one query) exceeds the time limit of the runner (`FILE_TIMEOUT`,
  900 s): the tuples of the model are lists, so a row of many columns is slow to build.
  The extracted OCaml interpreter (`tools/extraction/build.sh`) did not finish it in 72 minutes either: the
  cost is in the semantics (nested semi-joins over list-based tuples), not in `vm_compute`.
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

Run 14 (iteration 25, the commit `0e36d0b` with the fix of the runner of TODO 8.36): **517** translated, **15** fail,
1 not run (`numeric:754`, over the limit of a case: `numeric.sql` is now compiled case by case when it goes over the
limit of its file). The 37 cases which pass since run 12 (53 failing; the 38th, `numeric:754`, is the one not run), none newly failing: `to_char` of numbers (TODO 8.12), the
padding of the psql tables (TODO 8.33), integers in bases 16, 8 and 2, `numeric` and doubles with an exponent,
the literals of `VALUES`, `%` and `log` on the special `numeric` values (TODO 8.32). The 15 left: the `-0` of
`power ('-inf'::numeric, -3)` and the products of special values of `numeric:563` (the special `numeric` values
are doubles), `exp (1234.5678)` and `10::numeric ^ 131071` (the precision and the size of very long decimals,
TODO 8.15), `rank ('3') WITHIN GROUP` of a text argument, `concat` of a date (`DateStyle`), the spaces of two
`json` texts, `GROUPING` in a subquery, `power (float8 '-inf', float8 '-2') = '0'` (NULL given), four window
queries.

Run 11 (iteration 12): the infinite dates and timestamps and the special inputs (`today`, ...): **53** fail (the 16
cases of `date` and `timestamp` pass; the other files are those of run 10).

Run 10 (iteration 9, TODO 8.11): `NaN` and the infinities of `numeric` are represented by the special values of the
doubles (`'NaN'::numeric`, the casts between `numeric` and the floats, `power`, the arithmetic by a string literal,
which is read as a `numeric`); the variances and the statistics of two variables are NaN on such inputs: **69** fail
(51 fewer). What still fails: 30 `to_char` with numeric format models, 16 infinite dates and timestamps, 12 others of
`numeric` (the scales of `sqrt`, `ln`, `log` in queries which also hold special values, `exp` beyond 77 digits), 3
window results which depend on the order of the peers, 2 `DateStyle`, and 6 others.

Run 9 (iteration 7, TODO 8.13): the dates before the common era (`BC`, `EXTRACT` of negative years, the Julian
day): **120** fail (13 fewer than run 8; the files `date` and `timestamp` were run again, the others are those of
run 8). The calendar conversions were off by one day before 0000-03-01: fixed.

Run 8 (iteration 6 of `docs/ITERATIONS.md`, TODO 8.9; `strings` and `jsonb` are now read): **514** queries
translated, **133** fail (238 of the same 514 failed before the fixes of this run). Fixed, each from the source of
PostgreSQL: the widths of `format` (`text_format`, 17 cases); `json_strip_nulls` of a literal and its second argument
(14); `x = ANY ('{1,2,3}')`, a literal read as an array of the type of `x` (8); the doubles are compared as
`float8out` prints them, and `power`, `exp` and the division follow `dpow`, `dexp` and `float8_div` on NaN and the
infinities (40); `power` of `numeric` has the scale of `power_var` and non-integer exponents (20); a grouping
expression which is a condition is hidden in the groups which do not group it, also in `HAVING` (2;
`sexpr_eqb` compared only constants, columns and functions); `generate_series` of an integer cast to `numeric` (3:
the cast gave a rational, it gives a `numeric` of scale 0). What still fails: 45 `NaN` / `Infinity` of `numeric`
and 16 `infinity` dates and timestamps (not representable), 28 `to_char` with numeric format models, 12 BC dates,
14 aggregates over `NaN` / `Infinity`, 3 window results which depend on the order of the peers, 2 `concat` of a date
(`DateStyle`), and 13 others (`exp` of a `numeric` with more than 77 digits, the type of an `unknown` literal,
`EXTRACT (JULIAN ...)`, the order of `json_object_agg`, psql's display).

Run 6, after TODO 5.1 (window functions, `VALUES`, grouping sets, views, typed literals, `COPY ... FROM stdin`):
**459** queries translated, **234** fail (run 7, after the fixes of numeric modulo and casts: **215**); 103 of them are `NaN`/`Infinity` (not representable), 67 the scale of `power` on
`numeric` (the precision rule of `power_var` is not modelled), 26 `to_char` with numeric format models, 17 `format` widths,
14 `json_strip_nulls`, 12 BC dates, 8 array literals in `ANY`; the others are listed below. Found and fixed by the runs: the
text of a decimal with more than 40 decimals (it printed `0.000...`), the population variance of one value, the memory
blow-up of exact powers with huge exponents, `numeric` modulo, the cast of a `numeric` to an integer (it was NULL).

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

**MariaDB test suite** (`MariaDB`, TODO 5.2): `tools/spec/suite_run.sh MariaDB mariadb RESULT_FILES` replays
`mysql-test/main` (`MariaDB/server`) with `sql2coq.py --lenient`: a script is replayed up to its first loop, variable,
connection or change of `sql_mode`; the lines printed by `--echo` are not rows. Run 2 (the files `win*`, `cte_*`,
`intersect*`, `except*`, `fetch_first`, `func_math`, `func_str`, `select`, `group_by`, `having`, `union`, `subselect`):
**346** queries translated, **339** pass. The 7 failures:

| Case | Reason |
|---|---|
| `win_sum:3`, `win_avg:3` | MariaDB computes a window `SUM`/`AVG` over a moving frame incrementally on doubles (the row which enters is added, the row which leaves is subtracted: `Item_sum_sum::add`, `remove`), so the result carries the rounding of that order (`1.0999999999999996`); the model sums each frame (`1.1`). The order of the additions is not specified by SQL: an engine-specific rounding, not modelled |
| `win_percent_cume:2`, `:3` | MariaDB prints `PERCENT_RANK` and `CUME_DIST` as doubles with 10 fixed decimals; the model computes them exactly (rationals) |
| `win_percentile:60` | `MEDIAN (x) OVER ()`: the ordered-set aggregates are modelled, not as window functions |
| `win_empty_over:2` | `ROW_NUMBER () OVER ()`: the numbering of the rows is not specified (no `ORDER BY`) |
| `group_by:286` | `DATE ('20050606')`: a string of digits read as a date; fixed after the run (`my_ts_of`) |

Run 4 (iteration 8, after the translator forgets the options of earlier tables of the same name): **396** queries
translated, **7** fail (the cases of the table above without `group_by:286`, and `win_percentile:59`, the same
`MEDIAN ... OVER ()` through a view); `subselect` (23 cases) is not run (memory limit of 5 GB).

Non-recursive `WITH` (since the run above; TODO 5.6): `cte_nonrecursive.result` and `cte_nonrecursive_not_embedded.result`, 37 queries translated, 37 pass.

Found and fixed by the MariaDB runs: the decimals of `VARIANCE`/`STD` (argument decimals + 4, 20 cases), the maximal
scale of `ROUND`/`TRUNCATE` (38; a scale of `2147483640` exhausted memory), several statements on one line.

**MySQL test suite** (`MySQL`, TODO 5.2): `mysql-test/r` of `mysql/mysql-server` at `06bcb0e` (1548 result files),
`tools/spec/suite_run.sh MySQL mysql`. Run 2: **1122** queries translated, **118** fail. The groups: 44 regular expressions
with inline flags scoped to a group (`(?i:a)`, `((?-i)a)`) or back references beyond `\9` (the leading flags `(?i)` are
modelled since this run); 15 views changed through `UPDATE`/`INSERT` (the translator now marks the tables of a view
unreliable: 2 remain); 9 `CURRENT_ROLE ()` and other session state; `INTERVAL ()` with a NULL bound, `varbinary`
(binary strings), locks, temporary tables, time zones: not modelled or server state.

Run 5 (iteration 18, the commit `afef183`): **1314** translated (103 of them expect an error), **89** fail (124 in
run 4, on the same cases). The 35 cases which pass now are regular expressions: the syntax errors of ICU (`a**`,
`a{37,17}`, a reference to a group which does not exist, a lookbehind without bound), `(?-i)`, atomic groups,
comments, `\10`, the groups of a lookahead. 4 cases of `regular_expressions_func` remain (`(?x)`, a set operation
of ICU).

**TiDB integration tests** (`TiDB`, TODO 5.2): `tests/integrationtest/r` (273 files), `suite_run.sh TiDB tidb`; a script
stops at the first change of `sql_mode`, collation, character set or time zone (the tests of the new collation framework
start with one). Run 2: **1935** translated, **125** fail, 2 files over the memory limit. The groups: 38 timestamp
literals with a time zone offset (`TIMESTAMP '2024-01-01 14:00:00+01:00'`, MySQL 8.0.19): not modelled; 31 JSON functions on
non-JSON arguments, where TiDB reports an error that the model gives as a value; integer overflow errors (`ABS (-2^63)`):
the integers of the MySQL family are unbounded in the model; results which hold a statement of the script (scripts
without `;` echo): harness.

Run 3 (iteration 9; the translator forgets the options of earlier tables of the same name, and the models of
iterations 6 to 9): **2095** translated, **128** fail, 1 file (13 cases) over the memory limit. The groups: 38 of
`time` (`DAYNAME (d) + 0`, a name used as a number, and the literals with a time zone offset), 31 JSON functions on
arguments which are not JSON (an error in TiDB and in MySQL, a value in the model), 15 `misc` (date literals with
other delimiters, `TIMESTAMP '00:00:00'`), 10 `builtin` (`tan`, `cot`, `exp` of Go's `math`, which is not correctly
rounded; the overflow of `BIGINT`). Found by reading these: an error line of TiDB (`Error 1582 ...`) under a query of
one column was read as the header of an empty result, so that such cases expected no row (TODO 8.17).

**MySQL**, run 3 (same changes): **1211** translated, **95** fail.

Runs 4 (iterations 10 to 15): the queries which the engine rejects are cases (`mk_case_error`); the result files of
the same name are all checked; the fixes of the JSON functions, of the typed literals, of `DAYNAME`, of `INTERVAL`.
**TiDB**: **2102** translated (53 expect an error), **50** fail (8 of them expect an error), 1 file over the memory
limit. **MySQL**: **1314** translated (103 expect an error), **124** fail (31 of them expect an error): 39 regular
expressions (inline flags scoped to a group, invalid patterns which must be errors), 9 roles, 8 locks, and others of
the session and of the server. **MariaDB**, run 5: **428** translated (32 expect an error), **16** fail (9 of them
expect an error; they pass since iteration 17), `subselect` not run. **OceanBase**, run 21: **775** translated,
none fails, 1 file over the time limit.

Found and fixed by the MySQL-family runs: digit strings read as dates (`'20050606'`), the exponent of numeric strings
(`'123e-2'`), leading inline regular-expression flags, executable comments `/*!NNNNN ... */`, TiDB's error lines
(`Error 1582 (42000): ...`) and warning tables.

The table of all the runs is `docs/CONFORMANCE_SUMMARY.md` (`tools/spec/summary.py`).

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

**OceanBase, Oracle mode, the examples of the documentation** (TODO 5.5): `tools/spec/oradoc2result.py
oceanbase-doc OUTDIR` extracts the examples of the Oracle-mode pages (the statements after `obclient>`, the tables
which the client prints), `sql2coq.py --dialect OceanBaseOracle --lenient` translates them (the queries on tables
of other pages, the PL blocks and the functions the translator does not know are left out). 351 pages, 871 queries
with their results; **172 translated, 122 pass**. The 50 others:

| Cases | Reason |
|---|---|
| 14 | Irrational results printed with the 40 digits of `NUMBER` (`EXP`, `LN`, `LOG`, `SIN`, `COS`, `TAN`, `ASIN`, `ATAN`, `ATAN2`, `SQRT`, `CORR`, an `AVG` of `50 / 3`): the Oracle mode has no model of the precision of `NUMBER` for these functions (they are errors or doubles in the model) |
| 22 | Format models of `TO_CHAR` (`'99.99'`, `'9.9EEEE'`, `'FML999.99'`, ...), `TO_DATE`/`TO_TIMESTAMP` and the display of dates, timestamps and intervals (`11-NOV-21 11.11.11.110000000 AM`): not modelled; one (`TO_DATE ('2020', 'YYYY')`) takes the current month, the date when the page was written |
| 1 | `JSON_ARRAYAGG`: not modelled in Oracle mode |
| 1 | the string `'NULL'` and NULL print the same (`3, NULL, ...`): the harness reads the text `NULL` as NULL |
| 12 | pages whose examples are not one script: the states before and after an example shown separately (`INSERT`, `MERGE`, partitions, an `UPDATE` in a PL block, a trigger), and two pages on rules whose `SELECT 1 FROM DUAL` shows `2` (the result of a rule which the model does not have) |

Found and fixed by this run: `MEDIAN` interpolated the values in the order of the group, not in their sorted order;
`POWER` with a negative integer exponent was NULL.

The Oracle mode is not run against sqllogictest: the expected results were produced by SQLite,
MySQL and PostgreSQL, the scripts have no `skipif oracle`, and the Oracle division `/` is exact
(`61 / 88 * 96` is 0 in the recorded results, 66.5 in Oracle). The Oracle mode is checked
against the documentation and the source of the engine instead (`docs/DIALECTS.md`).

**Live engines** (TODO 5.7): `tools/spec/live_diff.py` generates tables and queries of the fragment, runs them on a
live engine and checks the model against its rows (the extracted interpreter). PostgreSQL 16.15, SQLite 3.45 and MariaDB 10.11,
1000 queries each: 915, 906 and 909 translated, **0 differences**.

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
