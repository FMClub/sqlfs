# Logic bugs of the engines as regression cases (TODO 5.6)

Each entry of `tools/spec/engine_bugs/logic_bugs.json` is a confirmed logic bug (a wrong result) with its reproducer,
the wrong result of the engine and the **correct** result, as stated by the report, by the developers or by the test
of the fix (`correct_source`). `tools/spec/engine_bugs/run.sh` replays them against the dialects: the model must give
the correct result. *The model's results define the expected semantics; where an engine deviates, the deviation is
recorded here, not copied.*

| Engine | Bug | Found by | Wrong result | Correct result (source) | Model |
|---|---|---|---|---|---|
| TiDB | [#38756](https://github.com/pingcap/tidb/issues/38756) | Pinolo | `SELECT DISTINCT SQRT(1) FROM t` is `5e-324` | `1` (test `TestIssue38756` of the fix, PR #50020) | correct |
| TiDB | [#40015](https://github.com/pingcap/tidb/issues/40015) | Pinolo | `DATE_ADD(BIN(c1), INTERVAL 1 DAY_HOUR)` over a join `ON (0 AND c1 != 1) IS FALSE`: four NULLs | two `2010-11-11 01:00:00`, two NULLs (test `TestIssue40015`, PR #41786) | correct |
| MariaDB | [MDEV-30255](https://jira.mariadb.org/browse/MDEV-30255) | Pinolo | `(SELECT (c1 DIV 1)*0.1 FROM t) UNION ALL (SELECT '1')` shows `0` | `0.0` (`type_newdecimal.result` of commit `da20c1754`) | correct |
| MySQL | [#119321](https://bugs.mysql.com/bug.php?id=119321) | ValScope | `SUM(DISTINCT c4)` with `DENSE_RANK() OVER` and `NOT REGEXP_LIKE` is NULL | `36` (ValScope, OSDI 2026, Figure 1) | correct |
| MySQL | [#119402](https://bugs.mysql.com/bug.php?id=119402) | ValScope | `... EXCEPT ...` over a CTE with `LOG (c15)` loses the row `(NULL, 2023)` | `(NULL, 2003)`, `(NULL, 2023)` (stated by the report, "Verified as described" by a MySQL developer) | not replayed: `YEAR`, `TIME`, `SET`, `TINYBLOB` columns |
| MySQL | [#119695](https://bugs.mysql.com/bug.php?id=119695) | ValScope | `INNER JOIN cte ON EXISTS (...)` gives 21 rows `(1, 15)` | empty (stated by the report, "Verified as described" by a MySQL developer) | not replayed: `YEAR`, `TIME`, `SET`, `ENUM`, `BIT`, `BLOB` columns |

Sources of the bug lists: Pinolo's reports (`github.com/qaqcatz/impomysql_bugreports`: 14 MySQL, 14 MariaDB, 11 TiDB) and
ValScope's list (`github.com/linli1724647576/ValScope`: 23 MySQL, 10 MariaDB, 5 TiDB). All the MySQL (33) and MariaDB (24)
reports were read (bugs.mysql.com, jira.mariadb.org, November 2026). Only the bugs whose correct result is stated by a
fix, by the developers, or by the report and confirmed as described by a developer are included; the others, with the
reason for each:
- MySQL: the Pinolo bugs (109351 to 109407) were verified ("Thank you for the report and test case") without saying
  which of the two disagreeing results is correct, or closed with a release note that gives no value (109351); 109363
  is `0` against `-0`; 118846, 119329, 119350, 119399 are column names, not rows; 119323 and 119403 were fixed without
  the correct output of their query; 119322 is a duplicate whose correct values only the reporter gives; 119698's
  outputs are cut; the other ValScope bugs are "Verified as described" without the expected rows.
- MariaDB: none. 16 are confirmed or open without a fix and without a statement of the correct output (developers
  reduced them or explained the cause); 3 are duplicates of those; MDEV-37891, MDEV-38064 (column names) and
  MDEV-38063 (`BIT` display) are not row values; MDEV-37888 (fixed) is about the metadata of the result columns.
The open TiDB issues (#40011 to #40018 without a decision) are not included.

Making the replay possible needed: the composite interval units (`DAY_HOUR`, ...), the mathematical functions and
`DATE_ADD` in the translator, parenthesised set operations at the top of a statement, unnamed columns of derived tables.
