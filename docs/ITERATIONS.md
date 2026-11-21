# Iteration log

The work on this repository proceeds in iterations: finish a milestone, record it here, tidy the repository, audit
the code, list what the audit found (as items of `docs/TODO.md` or issues of `docs/OPEN_ISSUES.md`), and take the
next item. One entry per iteration, newest last.

| # | Milestone | Result | Audit findings (next items) |
|---|-----------|--------|-----------------------------|
| 1 | TODO 6.3: the evaluation of `SqlFull.v` does not depend on the names of the attributes | `src/data/sql/SqlRename.v`, `eval_rename`, whole syntax, no axiom; I10 resolved | — |
| 2 | Audit of the repository layout and of the documents | tracked `.pyc` removed; legacy files moved to `src/testing/legacy/`; statuses of `OPEN_ISSUES.md` brought up to date; D1 decided | TODO 8.1–8.8 (new Phase 8) |
