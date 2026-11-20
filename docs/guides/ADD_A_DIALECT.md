# How to add a dialect

A dialect is a value of the record `vsem` (`src/data/dialects/Dialects.v`): the tables of the predicates,
functions and aggregates by name, and the fields which parameterise the evaluation of `SqlFull.v` (NULL test,
truth of a value, comparison, order, canonical key of `GROUP BY`/`DISTINCT`, position of NULLs, accepted
constructs, literals, comparison coercions, unification of set-operation columns, table functions).
`dialect_of` turns it into the record `dialect` of the core, and `to_dialect` adapts a query to it.

## 1. A variant of an existing dialect

When the engine is a fork or a release of a modelled one, reuse it.

- *Same values, other constructs.* `src/data/dialects/Percona.v` is the smallest example: one line,
  `mysql_vs my_default_session "Percona Server for MySQL" my_supports`. `PolarDB.v` changes only `supports`.
- *Same family, other session.* `MariaDB.v` and `TiDB.v` give `mysql_vs` another `my_session` (default
  collation, padding, `sql_mode` flags, regular-expression library) and their own `supports`.
- *An older release.* Use `at_version d fam v` (`Versions.v`) instead of a new file; add the release of each
  construct to `introduced`.

## 2. A new dialect

1. Create `src/data/dialects/NAME.v`. Build the record with `mk_vsem` (see `SQLite.v` or `PostgreSQL.v`):
   start from the tables of `ValueKit.v` (`c_math_table`, `bit_table`, the string kit `skit` of
   `StringFuns.v`, `Aggregates.v`, `TemporalFuns.v`, `JsonFuns.v`, `SystemFuns.v`) and replace the entries
   whose behaviour differs. Every entry is `("name", fun (l : list value) => ...)`; a failure is
   `Value_Err "the engine's message"`, a NULL is the NULL of the result type.
2. `supports`: the constructs the engine accepts (`feature` in `SqlFull.v`); a query using another one is
   rejected by `accepted_by`.
3. Add the file to `src/_CoqProject` after the files it imports, then `coq_makefile -f _CoqProject -o Makefile`.
4. Tests: a `src/testing/Test_NAME.v` with the behaviours that distinguish the dialect (one `Example` per
   behaviour, `vm_compute; reflexivity`), and the same queries in `Test_Dialects.v` beside the others.
5. Provenance: describe each new table entry in a `docs/functions/*.md` row with its source (file of the
   engine, or manual page); `python3 tools/functions/check_provenance.py --write` must report 0 undocumented.
6. Closeout: add an extractor for the engine's function registry to `tools/functions/catalogue.py`, run
   `tools/functions/closeout.sh NAME SOURCE "description"`, and give a reason to every name it leaves.
7. Conformance: replay the engine's recorded results (`tools/spec/run.sh`, `suite_run.sh`, `pg_run.sh` or
   `slt2coq.py`) and explain every failure in `docs/CONFORMANCE.md`.
8. `docs/DIALECTS.md`: a section with the constructs, modelled or excluded with a reason.
