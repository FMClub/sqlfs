# Open issues

GitHub Issues are not enabled on this repository, so this file records the
**design and direction questions that need discussion**. Implementation-level
defects (NULL handling in aggregates, string comparison, the join order of
`SqlExt`, ...) have been fixed directly and are listed in
`docs/SQL_COVERAGE.md`; they are not repeated here.

Each entry gives the current state, why it cannot simply be changed, and the
options.

---

## I1. Two deviations from SQL in the core semantics of `Sql.v`

**Status: the multi-column `IN` is fixed; the empty-table aggregate is open.**

- **Fixed**: `(a, b) [NOT] IN (subquery)` is now compared component-wise
  (`in_match` in `src/logic/Formula.v`): the result is the conjunction of the
  comparisons of the components, each of them being UNKNOWN when one of its two
  values is NULL. A component which definitely differs makes the row
  comparison FALSE. The single-column case is unchanged. The proofs of
  `SqlAlgebra.v` only needed their congruence step updated (`in_match_eq`).
  Checked by `old_row_not_in` and `old_row_in_unknown` in
  `src/testing/Test_Audit.v`.
- **Open**: an aggregate query without `GROUP BY` returns no row on an empty
  table; SQL returns one (`SELECT count(*) FROM empty` is `0`). `make_groups`
  partitions the input rows, so an empty input has no group.

**Why the second one is still open**: the natural fix is to make `make_groups`
return one empty group for `Group_By nil` on an empty input. An experiment
shows that this breaks, besides the congruence lemma `make_groups_eq` (easily
repaired), the well-sortedness proof of `Sql.v` and about ten proofs of
`SqlAlgebra.v` which unfold `make_groups` (16 uses). It also changes the
derived operator `delta` (DISTINCT, defined by grouping on all the attributes)
when the sort is empty, and `SELECT *` with an empty group needs a defined
sort: the algebra translates it to a projection on `sql_sort`, while the
evaluator of `Sql.v` returns the empty tuple.

**Options**:
1. Make the change and redo the affected proofs, giving `SELECT *` over an
   empty group the sort of the query (most work, strongest result).
2. Keep `Sql.v` as "the proven fragment" (it agrees with SQL when the
   input of an aggregate query is not empty), and take `SqlFull.v` as the
   reference semantics (see I2).
3. Add the hypothesis "the input of an aggregate query without `GROUP BY`
   is not empty" to the equivalence theorem.

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

**Status: the dialects are modelled and checked against real engines; some features remain.**
PostgreSQL, MySQL, SQLite and OceanBase (MySQL and Oracle modes) are instances of the record
`vsem` (`src/data/dialects/`). Their behaviour is established from the documentation, from the
source code of OceanBase, and from results recorded by real engines (`docs/DIALECTS.md`,
`docs/CONFORMANCE.md`): 545 OceanBase queries (7 known deviations), and 9600 `random/expr`
queries of sqllogictest per dialect with no failure.

Still open:
- **Decimal scale**: a decimal keeps the number of decimals of its literal (`length(0.00)` is 4).
  `Value_Q` is a rational and forgets it; a value which carries its scale would also fix the
  display of `4/3` and the type of `sum` and `avg`.
- **Acceptance of a query**: the constructs and the names of functions, predicates and aggregates are
  checked (`accepted_by`); `ONLY_FULL_GROUP_BY` and the bare columns of SQLite (the value of an
  arbitrary row, or the row of the `min`/`max`) are not.
- **Constructs of the dialects which `SqlFull` does not have**: `RANGE` window frames with an
  offset, `ROLLUP`, `CUBE` and `GROUPING SETS` (PostgreSQL, OceanBase, Oracle), `WITH RECURSIVE`,
  `FETCH FIRST ... WITH TIES` and `PERCENT` (Oracle mode), `ORDER BY` inside `string_agg`.
- **Oracle mode** is checked against the documentation and the shared engine code, because the
  open-source repository of OceanBase has neither its parser nor recorded results for it.
- Dates and times, floating-point numbers, integer ranges, regular expressions, JSON.

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

**Status: resolved, except for `FreshAttr.v`.**

- Resolved: `make` at the top level now generates `src/Makefile` from
  `src/_CoqProject`; the generated `src/CoqMakeFile*` are no longer tracked.
- Resolved: the opam file requires Coq 8.15, as the README says.
- Resolved: a GitHub Actions workflow builds the library and checks the
  examples on every push to `main` and on every pull request.
- Open: `src/data/proof_of_concept/FreshAttr.v` contains an `Admitted`
  (`fresh_attr_is_fresh`) and is not in `_CoqProject`. Proving it needs the
  injectivity of the decimal printing of natural numbers and a pigeonhole
  argument; nothing in the build depends on it.
