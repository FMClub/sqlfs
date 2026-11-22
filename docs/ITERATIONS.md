# Iteration log

The work on this repository proceeds in iterations: finish a milestone, record it here, tidy the repository, audit
the code, list what the audit found (as items of `docs/TODO.md` or issues of `docs/OPEN_ISSUES.md`), and take the
next item. One entry per iteration, newest last.

| # | Milestone | Result | Audit findings (next items) |
|---|-----------|--------|-----------------------------|
| 1 | TODO 6.3: the evaluation of `SqlFull.v` does not depend on the names of the attributes | `src/data/sql/SqlRename.v`, `eval_rename`, whole syntax, no axiom; I10 resolved | — |
| 2 | Audit of the repository layout and of the documents | tracked `.pyc` removed; legacy files moved to `src/testing/legacy/`; statuses of `OPEN_ISSUES.md` brought up to date; D1 decided | TODO 8.1–8.8 (new Phase 8) |
| 3 | TODO 8.4: README | rewritten: what is formalised, main results, repository map, documents, checks | the conformance summary still lists failing cases (PostgreSQL 215, TiDB 125, MySQL 118): TODO 8.9 |
| 4 | TODO 8.5: `eval_rename` instantiated | the order-preservation hypothesis made it vacuous for the instance: removed; `eval_result_rename`; `Renaming.v` (`eval_rename_names` for every dialect); `Test_Rename.v` | I11 / TODO 8.10: the order of the stored rows depends on the column names |
| 5 | TODO 8.8, 8.10: old `TODO` comments, storage order | the join types of `SqlExt.v` are the same evaluation (comment corrected); I11 decided: kept and documented | next: 8.9 (failing conformance cases) |
| 6 | TODO 8.9 (PostgreSQL), 8.6 | PostgreSQL regression tests: 238 → 133 failing of 514 (`format` widths, `json_strip_nulls`, array literals of `ANY`, doubles on NaN / infinities, `power` of `numeric`, grouping expressions which are conditions); `docs/TODO.md` statuses as lists | TODO 8.11–8.15 |
| 7 | TODO 8.13: BC dates | eras in `parse_date` / `date_text`, `EXTRACT` on negative years, `JULIAN`; a bug of the calendar conversions for the days before 0000-03-01 (off by one) fixed; PostgreSQL: 120 failing of 514 | — |
| 8 | TODO 8.14: `INSERT IGNORE` and `NOT NULL` | implicit defaults in the translator; stale per-table options of earlier scripts forgotten; OceanBase suite: 775 translated, 0 failing, 1 file not run | MariaDB run again (396 translated, 7 failing); TODO 8.16 (found and done: the calendar conversions are proved inverse of each other) |
| 9 | TODO 8.11 (numeric part), 8.9 | `NaN` / infinities of `numeric`, aggregates over them, string literals by numbers; PostgreSQL: 69 failing of 514; TiDB and MySQL run again (2095 / 128, 1211 / 95) | TODO 8.17–8.21 (a bug of the reader of TiDB results, JSON argument errors, names used as numbers, date delimiters, `BIGINT` overflow) |
| 10 | TODO 8.17, 8.18, 8.20 | the reader of TiDB results and the cases which expect an error; JSON argument errors of the MySQL family; typed `TIMESTAMP` / `TIME` literals | TODO 8.22 (JSON path wildcards), 8.23 (fractional `INTERVAL`) |
| 11 | TODO 8.19, 8.23 | `DAYNAME (d)` as a number; `INTERVAL` of the MySQL family (`get_interval_value`); TiDB `time`: 38 → 1 failing | all the suites to be run again with the new cases (8.9) |
| 12 | TODO 8.11 (dates) | infinite dates and timestamps, special date inputs; PostgreSQL: 53 failing of 514 | — |
| 13 | TODO 8.24: tests of the translator | `tools/spec/test_sql2coq.py` (9 tests), in the continuous integration | — |
| 14 | TODO 8.25 (part), 8.26 | acceptance: aggregates in `GROUP BY`, `SELECT DISTINCT` ordered by an unselected expression; result files of the same name no longer overwrite each other (TiDB: 12 more files checked) | TODO 8.27 (`TRIM` forms), 8.28 (replay of the scripts) |
| 15 | TODO 8.21, 8.27 | `ABS` / `ROUND` out of the range of `BIGINT`; `TRIM (LEADING FROM s)` | — |
| 16 | TODO 8.29: the relation theorems of 6.1 and 6.3 | two hypotheses (`Hu`, `Hperm`) were false for the instance: replaced by ones which hold; `Test_Relate.v` instantiates `sql_full_agree3` | TODO 8.30 (`Hnull` and the typed NULLs) |
| 17 | TODO 8.25 (windows) | acceptance: `NTILE (0)`, frames which start after their end, `LAG` / `LEAD` without `ORDER BY` in MariaDB; the extracted interpreter still builds and agrees with `vm_compute` on two files | — |
| 18 | TODO 8.25 (regular expressions) | syntax errors of the regular expressions (`a**`, `{37,17}`, ICU: unknown group, unbounded lookbehind); scoped `(?-i)`, atomic groups, comments, `\10`, groups of a lookahead; an example of `Test_Closeout.v` gave PostgreSQL an option inside an expression, which it rejects | — |
| 19 | TODO 8.22 | JSON paths of the MySQL family: `.*`, `[*]`, ranges, `last`, `**`, the wrapping of a non-array; `JSON_EXTRACT` with several paths | — |
| 20 | TODO 8.12 | PostgreSQL `to_char (number, format)`: a model of `formatting.c` (`PgNumFormat.v`), checked on the examples of the manual and on `numeric.sql` | — |
| 21 | TODO 8.32, 8.34 | PostgreSQL texts of numbers: integers in bases 16, 8, 2 with underscores, `numeric` with an exponent, string literals of `VALUES`, `%` on NaN; the runners compile a file over its time limit case by case | 8.34 (found: a newly computable case made a whole file time out) |
| 22 | TODO 8.31 | `PERCENT_RANK` and `CUME_DIST` typed by dialect (`vs_of_rat`): doubles, 10 decimals in MariaDB, exact in Oracle mode | — |
| 23 | TODO 8.25 (windows) | MariaDB's mandatory `ORDER BY` for the ranks; `RANGE` frames over other than one sort key; the queries of another mysqltest connection are not translated (privileges) | — |
| 24 | TODO 8.32 | PostgreSQL: doubles with an exponent, `log (b, x)` of `numeric` on NaN and the infinities | the `-0` of `power ('-inf'::numeric, -3)`: a limit of the representation of the special `numeric` values |
| 25 | TODO 8.35: audit of iterations 18 to 24 | `JSON_TABLE` row paths with wildcards inside them (`my_seek`); generated tables and conformance summary brought up to date | — |
| 26 | TODO 8.37 (fixes of the audit after PR 74) | literals compared with numbers and in hypothetical aggregates; `GROUPING` in a subquery (with proofs); specials of `numeric`; `exp` and large powers; the order-dependent window functions and aggregates; MariaDB's `MEDIAN`; the DateStyle of PostgreSQL's regression database | BC dates of the translator, `make_date` with a negative year (found by checking the BC dates) |
| 27 | TODO 9.1, 9.2, 9.7 (part), 9.9-9.11, 9.19, 9.20 | the session changes followed (a dialect per case), `WITH RECURSIVE`, MySQL functions, static errors and harness, explicit `vs_client` / `ms_engine`, stable case identifiers, UTF-8 strings up to U+02FF with lengths in characters; TiDB 2739 translated, MySQL 1591, no case which passed fails | TODO 9.25 (the TiDB cases which 9.1 shows), 9.9b (`STR_TO_DATE`); found: `CHAR_LENGTH` and `SUBSTRING` counted bytes |
