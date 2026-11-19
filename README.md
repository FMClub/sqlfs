# SQLFormalSemantics

A Coq mechanized executable formal semantics for realistic SQL queries.


## Compilation
This work compiles with Coq 8.15.0:
```
make
make install
```


## SQL coverage

`src/data/sql/Sql.v` is the fragment proven equivalent to the extended
relational algebra. `src/data/sql/SqlFull.v` extends its syntax and gives an
executable semantics to the rest of the query language: outer and lateral
joins, `DISTINCT`, set operations with and without `ALL`, `ORDER BY` /
`OFFSET` / `LIMIT`, subqueries and conditions inside expressions, `CASE`,
`FILTER` and `DISTINCT` aggregates, window functions, `WITH` and `VALUES`.
The values, predicates, functions and aggregates are in
`src/data/proof_of_concept/Values.v`.

- [docs/SQL_COVERAGE.md](docs/SQL_COVERAGE.md): audit of the formalisation
  against SQL, what is covered, and the conventions of the semantics.
- [docs/OPEN_ISSUES.md](docs/OPEN_ISSUES.md): open design questions.
- `src/testing/Test_SqlFull.v`, `src/testing/Test_Audit.v`: examples checked
  by computation during the build.

To build from a fresh clone:
```
cd src
coq_makefile -f _CoqProject -o Makefile
make
```


## License

This code is released under the terms of the [Creative Common
Attribution-NonCommercial-NoDerivatives 4.0 International
license](https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode);
see LICENSE for details.


## Companion paper
[A Coq mechanised formal semantics for realistic SQL queries: formally reconciling SQL and bag relational algebra](https://hal.archives-ouvertes.fr/hal-01955433), Benzaken, Véronique; Contejean, Évelyne, [CPP - 8th ACM SIGPLAN International Conference on Certified Programs and Proofs](https://popl19.sigplan.org/track/cpp-2019) - 2019
