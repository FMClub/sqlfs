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
| 8 | TODO 8.14: `INSERT IGNORE` and `NOT NULL` | implicit defaults in the translator; stale per-table options of earlier scripts forgotten; OceanBase suite: 775 translated, 0 failing, 1 file not run | the MySQL-family suites translate more cases now: to be run again (8.9) |
