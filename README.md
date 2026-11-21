# SQLFormalSemantics

A Coq mechanized executable formal semantics for realistic SQL queries.


## Compilation
This work compiles with Coq 8.15 (checked with 8.15.2). `make` generates
`src/Makefile` from `src/_CoqProject` with `coq_makefile`, then builds the
library and checks the examples of `src/testing`:
```
make
make install
```


## What is formalised

- `src/data/sql/Sql.v`, `SqlAlgebra.v`: the fragment of the companion paper, proven equivalent to the extended
  relational algebra.
- `src/data/sql/SqlFull.v`: an executable semantics of the query language of real engines: joins (outer, lateral),
  set operations, subqueries, `CASE`, aggregates with `FILTER` / `DISTINCT` / `ORDER BY`, grouping sets, window
  functions, `ORDER BY` / `OFFSET` / `FETCH`, `WITH [RECURSIVE]`, table functions, and failures as values.
- `src/data/dialects/`: the dialects as records (`dialect`): PostgreSQL, MySQL, MariaDB, TiDB, Percona Server,
  PolarDB, SQLite, OceanBase (MySQL and Oracle modes), with their functions, types, collations and versions.

## Main results

| Result | File | Statement |
|---|---|---|
| `sql_query_to_alg_is_sound` | `src/data/sql/SqlAlgebra.v` | a query of `Sql.v` and its translation to the algebra have the same bag |
| `sql_full_agree3`, `sql_full_alg3` | `SqlRelateSelect.v`, `SqlRelateAlg.v` | on the fragment of `Sql.v`, `SqlFull.v` gives the same bag as `Sql.v` and as the algebra |
| `eval_sorts` | `SqlSorts.v` | the rows of a query have the attributes of its sort |
| `scope_query` | `SqlScopeQuery.v` | a query depends on the enclosing blocks only through the columns it names |
| `eval_congruence`, `dialect_refinement` | `SqlCongruence.v`, `dialects/Refinement.v` | two dialects which agree on what a query uses give it the same rows |
| `eval_rename`, `eval_rename_names` | `SqlRename.v`, `dialects/Renaming.v` | the evaluation does not depend on the names of the attributes |
| `rollup_as_grouping_sets`, frame and set-operation laws | `SqlGroupFacts.v`, `SqlFullFacts.v` | laws of the constructs |
| TLP, NoREC, containment | `Oracles.v`, `SqlFullFacts.v` | the oracles of the testing tools hold in the semantics |

`src/testing/Assumptions.v` prints the assumptions of these results (no axiom); `AssumptionsExt.v` those of the
results which use functional extensionality, and nothing else.

## Repository map

| Path | Content |
|---|---|
| `src/common`, `src/terms`, `src/logic` | ordered sets, finite sets and bags, terms, three-valued logic, formulas |
| `src/data/flat` | tuples, environments and well-formedness of the paper's language |
| `src/data/sql` | the two semantics and their theorems (see above) |
| `src/data/dialects` | the dialect records, their function tables, typing, versions, result texts |
| `src/data/proof_of_concept` | the instance of the values (`Values.v`), dates, JSON, IEEE floats, concrete syntax |
| `src/testing` | examples checked by computation during the build; `slt/`: sqllogictest samples; `legacy/`: files of the original development which are not built |
| `tools/spec` | the SQL front end (`sql2coq.py`, `slt2coq.py`, `sqlprint.py`) and the conformance runners |
| `tools/functions`, `tools/docs`, `tools/collation` | generators and checks of the function tables, of `docs/DIALECT_TABLES.md`, of the collation weights |
| `tools/extraction` | the extracted interpreter (`tools/sqlfs_run.py` drives it) |
| `docs` | see below |

## Documents

- [docs/SQL_COVERAGE.md](docs/SQL_COVERAGE.md): what is covered, the conventions, the deviations of `Sql.v`.
- [docs/DIALECTS.md](docs/DIALECTS.md), [docs/DIALECT_TABLES.md](docs/DIALECT_TABLES.md): the dialects and their
  tables; [docs/guides](docs/guides): how to add a dialect, how to read a rule.
- [docs/CONFORMANCE.md](docs/CONFORMANCE.md), [docs/CONFORMANCE_SUMMARY.md](docs/CONFORMANCE_SUMMARY.md): the runs
  against the test suites of the engines, with the failures; [docs/ENGINE_BUGS.md](docs/ENGINE_BUGS.md).
- [docs/TODO.md](docs/TODO.md): the plan and the status of each item; [docs/OPEN_ISSUES.md](docs/OPEN_ISSUES.md):
  design questions and their resolutions; [docs/ITERATIONS.md](docs/ITERATIONS.md): the log of the iterations.

## Checks

The continuous integration (`.github/workflows`) runs, and so can you:
```
make                                              # the library and the examples of src/testing
(cd src && coqc -R . SQLFS testing/Assumptions.v) # no "Axioms:" in the output
python3 tools/check_hygiene.py                    # no Admitted, no Axiom, the core imports no dialect
python3 tools/functions/check_provenance.py       # every function of the tables has a source
python3 tools/spec/sqlprint.py --dialect MySQL tools/spec/roundtrip_samples.sql
```


## License

This code is released under the terms of the [Creative Common
Attribution-NonCommercial-NoDerivatives 4.0 International
license](https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode);
see LICENSE for details.


## Companion paper
[A Coq mechanised formal semantics for realistic SQL queries: formally reconciling SQL and bag relational algebra](https://hal.archives-ouvertes.fr/hal-01955433), Benzaken, Véronique; Contejean, Évelyne, [CPP - 8th ACM SIGPLAN International Conference on Certified Programs and Proofs](https://popl19.sigplan.org/track/cpp-2019) - 2019
