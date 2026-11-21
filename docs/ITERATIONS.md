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
