# Open issues

GitHub Issues are not enabled on this repository, so this file records the
**design and direction questions that need discussion**. Implementation-level
defects (NULL handling in aggregates, string comparison, the join order of
`SqlExt`, ...) have been fixed directly and are listed in
`docs/SQL_COVERAGE.md`; they are not repeated here.

Each entry gives the current state, why it cannot simply be changed, and the
options.

---

## I1. Two deviations from SQL in the core semantics of `Sql.v`, which the equivalence proof depends on

**Current state** (both machine-checked by `old_aggregate_empty` and
`old_row_not_in` in `src/testing/Test_Audit.v`):

- An aggregate query without `GROUP BY` returns no row on an empty table; SQL
  returns one (`SELECT count(*) FROM empty` is `0`). `make_groups` partitions
  the input rows, so an empty input has no group.
- A multi-column `(a, b) [NOT] IN (subquery)` is UNKNOWN as soon as any
  component is NULL; SQL compares component-wise, and the row comparison is
  FALSE when one component definitely differs.

**Why it was not changed**: these two definitions (`eval_sql_query`,
`eval_sql_formula`) are used directly by `SqlAlgebra.v` (about 3800 lines: the
equivalence between SQL and the extended relational algebra). Changing them
requires redoing the affected proofs.

**Options**:
1. Change `Sql.v` / `Formula.v` and redo the affected proofs of `SqlAlgebra.v`
   (most work, strongest result).
2. Leave `Sql.v` as it is, present it explicitly as "the proven fragment",
   state these two deviations in the documentation, and take `SqlFull.v` as the
   reference semantics.
3. Add hypotheses to the equivalence theorem (non-empty input, single-column
   `IN`) under which the current proof is kept.

## I2. No theorem relates `SqlFull.v` to the existing results

**Current state**: `SqlFull.v` is a new syntax and executable semantics. Its
correctness currently rests on about 130 examples checked by computation
(`Test_SqlFull.v`, `Test_Audit.v`) and on the properties of
`SqlFullFacts.v`. Its relation to `Sql.v` and to the relational algebra is
**not proven**.

**Directions to decide**:
- Whether to prove an embedding theorem: a query of `Sql.v`, translated to
  `SqlFull`, has the same semantics (excluding the two deviations of I1, and
  dealing with bags vs. lists and with `N_join_bag` vs. the cross product).
- Whether to extend the algebra (`SqlAlgebra.v` / `SqlAlgebraExt.v`) to outer
  joins, DISTINCT, ordering and windows, and to prove a translation from
  `SqlFull` correct. This is the natural extension of the main theorem of the
  paper, but it is a large amount of work, and the set of constructs to cover
  has to be chosen first.
- `SqlExt.v` (the JOIN extension) overlaps with `SqlFull.v`: merge them, keep
  one, or make `SqlExt` a subset of `SqlFull`?

## I3. Runtime errors are modelled by NULL

**Current state**: the semantics is a total function. Division by zero, an
invalid cast, and a scalar subquery returning several rows are runtime errors
in SQL; here they all yield NULL.

**Problem**: this differs from most database systems (a query that fails is
given a result).

**Options**: (a) keep this and state it in the theorems; (b) make evaluation
return an `option` / error monad, with error propagation in every definition
and proof; (c) define a separate static or dynamic "does not fail" predicate,
and state the theorems for the queries which satisfy it.

## I4. Named tuples vs. the positional semantics of SQL

**Current state**: a tuple is a finite map from attribute names to values.
Consequently:
- set operations require the same attribute names on both sides (SQL matches
  columns by position);
- a result cannot have two columns with the same name, and a self-join needs
  an explicit renaming;
- attributes with the same name in a `FROM` clause are merged silently (A6 in
  `SQL_COVERAGE.md`).

**To decide**: introduce a positional or qualified column model (this affects
`Tuple.Rcd` and every proof above it), or keep the named model and provide a
front end which normalises real SQL into the "pairwise distinct attributes"
form, together with a statement of its correctness.

## I5. No static typing, no well-formedness check

**Current state**: queries have no type system. A comparison between values
of different types is UNKNOWN, arithmetic over a non-number is NULL, and a
non-grouped column in the `SELECT` of a grouped query takes its value from the
first row of the group. NULLs are typed (`Value_Z None` and
`Value_string None` are different values); they are currently normalised to
the type of the attribute when a tuple is built.

**To decide**: whether to define type checking and well-formedness (as
`WellFormed.v` does for the former language), and to restrict the correctness
statements to well-formed queries. The rule which says to which query block an
aggregate belongs is currently syntactic (the block which binds one of its
columns), and differs from the `find_eval_env` of the former code; it should be
settled by the same definition.

## I6. Dialect-dependent choices are hard-wired

**Current state**: the following are implementation-defined in the SQL
standard, and are fixed here to the behaviour of PostgreSQL: NULLs are the
largest values in an ordering; integer division truncates towards zero; `avg`
returns an exact rational; `GREATEST` / `LEAST` ignore NULLs; a `LIMIT`
without a total order returns one determined result.

**To decide**: whether to make these parameters (a "dialect" record), so that
the same theorems can be instantiated for several database systems.

## I7. SQL features which are not covered

In the expected order of difficulty; priorities are to be decided:
- recursive CTEs (`WITH RECURSIVE`): termination is not guaranteed, so this
  needs a fuel parameter or a condition for the existence of a fixpoint;
- `GROUPING SETS` / `ROLLUP` / `CUBE`;
- `RANGE` window frames with a numeric offset, frame exclusion;
- date/time types, floating-point numbers, collations;
- ordered-set aggregates (`percentile_cont`, ...), aggregates with several
  arguments, `ORDER BY` inside `string_agg`.

## I8. Build and repository maintenance

- The top-level `Makefile` runs `cd src; make`, but `src/Makefile` is ignored
  by `.gitignore`, so a fresh clone cannot run `make` directly; the committed
  `src/CoqMakeFile*` are generated files and contain machine-specific paths.
- `coq-sqlformalsemantics.opam` requires Coq 8.11.2, the README says 8.15.0
  (this work was checked with 8.15.2).
- `src/data/proof_of_concept/FreshAttr.v` contains an `Admitted` and is not in
  `_CoqProject`.
- There is no CI; a workflow which compiles every file, tests included, is
  suggested.
