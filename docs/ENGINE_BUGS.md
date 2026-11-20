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

Sources of the bug lists: Pinolo's reports (`github.com/qaqcatz/impomysql_bugreports`: 14 MySQL, 14 MariaDB, 11 TiDB, with
reproducers but without saying which result is correct) and ValScope's list (`github.com/linli1724647576/ValScope`: 23 MySQL,
10 MariaDB, 5 TiDB identifiers). Only the bugs whose correct result is stated by a confirmed fix or by the developers are
included. Open: the report pages of `bugs.mysql.com` and `jira.mariadb.org` could not be fetched from the development
environment (its network blocks them), so the other confirmed MySQL and MariaDB bugs wait for that access; the open TiDB
issues (#40011 to #40018 without a decision) are not included.

Making the replay possible needed: the composite interval units (`DAY_HOUR`, ...), the mathematical functions and
`DATE_ADD` in the translator, parenthesised set operations at the top of a statement, unnamed columns of derived tables.
