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

**Status: resolved (TODO 1.1).** A failure is a value (`Value_Err`, dialect fields `is_error`,
`error`); functions propagate it (lazily for `COALESCE`, `IF`, `NVL2`, ...: only their first
argument); `scond_raises` says whether a condition fails (a connective fails only if the other
operand does not decide the result, since SQL leaves the order of evaluation unspecified); every
operation which drops rows keeps the failed ones (`keep_errors`, `err_row`), so a failure is never
lost; `eval_query_result` returns `QR_Error` or `QR_Rows`. Errors produced: division and modulo by
zero and invalid casts in PostgreSQL; division by zero and `ORA-01722` (invalid number, also in
comparisons) in Oracle mode; a scalar subquery with several rows (but SQLite takes the first row);
a recursion which does not terminate within `rec_fuel`. Integer overflow comes with TODO 1.2.3.
The kind of an error is kept in the value but not compared with the engine's message.

**Former state**: the semantics was a total function. Division by zero, an
invalid cast, and a scalar subquery returning several rows are runtime errors
in SQL; here they all yielded NULL.

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
  checked (`accepted_by`). A bare column (neither grouped nor aggregated, in a block with
  aggregates or `GROUP BY`) is the feature `F_Bare_Column`: rejected by PostgreSQL, MySQL
  (default `ONLY_FULL_GROUP_BY`) and Oracle mode, accepted by SQLite and OceanBase MySQL mode. The check is
  syntactic: functional dependencies (keys) are not modelled, so a query which groups by a
  primary key and selects other columns is rejected although PostgreSQL and MySQL accept it;
  subqueries are not inspected; the value of a bare column in SQLite (an arbitrary row, or the
  row of the `min`/`max`) is still not modelled.
- **Constructs of the dialects which `SqlFull` does not have**:
  `ORDER BY` inside `string_agg`.
- **Oracle mode** is checked against the documentation and the shared engine code, because the
  open-source repository of OceanBase has neither its parser nor recorded results for it.
- Dates and times, floating-point numbers, integer ranges, regular expressions, JSON.

## I7. SQL features which are not covered

In the expected order of difficulty; priorities are to be decided:
- (done) recursive CTEs: `SQ_WithRec` iterates the step on the working table (`UNION ALL` appends, `UNION` keeps only new rows and stops on a fixpoint); the number of steps is bounded by `rec_fuel` (1000, as MySQL's `cte_max_recursion_depth`), so a non-terminating recursion returns the rows of the first 1000 steps instead of an error; mutual and multiple recursion are not modelled;
- (done) `GROUPING SETS` / `ROLLUP` / `CUBE` / `GROUPING()`: grouping expressions that a set does not group read as NULL;
- (done) `FETCH FIRST n [PERCENT] ROWS ONLY | WITH TIES` (`SQ_Fetch`): `WITH TIES` is accepted by PostgreSQL and Oracle mode, `PERCENT` (rounded up, computed before the offset) by Oracle mode only;
- (done) `RANGE` window frames with integer offsets (`Frame_Range`): single numeric ORDER BY key, descending order mirrored, NULL keys are peers of each other only; decimal offsets, `INTERVAL` offsets and frame exclusion are not covered;
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

## I9. Completeness ledger

**Status: open.** The goal is a formal semantics of queries with no gap, for PostgreSQL, MySQL,
SQLite, OceanBase (two modes), MariaDB, TiDB, Percona Server and PolarDB. This ledger lists each
known gap and its status; it is updated by every pull request which touches one of them.

| # | Gap | Status |
|---|---|---|
| 1 | Aggregate home block, correlated subqueries | resolved (PR #7) |
| 2 | Names of functions, predicates and aggregates are checked per dialect | resolved (PR #7); arities of functions checked, unknown functions are errors (TODO 2.10) |
| 3 | `GROUPING SETS`, `ROLLUP`, `CUBE`, `GROUPING()`, `ORDER BY` under grouping sets | resolved (PR #8, tests of `ORDER BY` added later) |
| 4 | `WITH RECURSIVE` | resolved, bounded by `rec_fuel` (PR #9); mutual recursion not modelled |
| 5 | Bare columns (`ONLY_FULL_GROUP_BY`) | resolved for acceptance (PR #10); the value of a bare column in SQLite/MariaDB/OceanBase is not modelled; no functional dependencies |
| 6 | `RANGE` frames with integer offsets | resolved (PR #10); decimal and interval offsets, frame exclusion open |
| 7 | `FETCH FIRST ... WITH TIES`, `PERCENT` | resolved (PR #11) |
| 8 | MariaDB, TiDB, Percona, PolarDB: constructs, default collation, `sql_mode` | resolved for the constructs of `SqlFull` (PR #12); their functions beyond those of MySQL, and MariaDB's Oracle mode, open |
| 9 | `PERCENT_RANK`, `CUME_DIST` | resolved (rational values) |
| 10 | Decimal scale (`length(0.00)`, `4/3 = 1.333333333` in OceanBase) | resolved (TODO 1.2.1) |
| 11 | Floating-point numbers (IEEE rounding, `NaN`, `Infinity`, `-0`) | resolved (TODO 1.2.2); `BINARY_DOUBLE` of Oracle mode, `extra_float_digits` other than 1 and `REAL_AS_FLOAT` open |
| 12 | Dates, times, timestamps, intervals, time zones | resolved except time zones other than UTC (TODO 1.5) |
| 13 | Integer ranges, overflow, `BIGINT UNSIGNED` | resolved (TODO 1.2.3) |
| 14 | Runtime errors (division by zero in PostgreSQL, invalid casts) are NULL here (I3) | resolved (TODO 1.1) |
| 15 | Regular expressions (`~`, `REGEXP`, `REGEXP_LIKE`, `REGEXP_REPLACE`) | resolved (TODO 2.4, `docs/functions/regex.md`); groups of PostgreSQL's equal-length alternatives, `regexp_match(es)` (arrays), the `x` flag open |
| 16 | JSON and arrays | JSON resolved for the core functions (TODO 1.6); arrays open |
| 17 | Collations beyond case folding and padding (accent folding, `utf8mb4_unicode_ci`, locale collations of PostgreSQL) | resolved for the MySQL family and SQLite (TODO 1.3); unresolved: `uca1400` tables (not in MariaDB's source), PostgreSQL ICU/libc collations, column-level collations |
| 18 | `ORDER BY` and separator inside `group_concat` / `string_agg` / `listagg` (`E_AggX`; aggregates `group_concat_sep`, `string_agg_sep`, `listagg_sep`) | resolved |
| 18b | Ordered-set aggregates (`percentile_cont`, `percentile_disc`, `mode`), other multi-argument aggregates | open |
| 19 | `DISTINCT ON` (derived form `distinct_on`, by `ROW_NUMBER`), `NATURAL` join (derived form `from_natural_join`, existing) | resolved as derived forms |
| 19b | `USING` joins, table functions (`generate_series`), `TABLE` as a statement | `USING`/`NATURAL` resolved (TODO 3.2, translator); table functions resolved (TODO 3.4, `Fr_Fun`); `TABLE t` is a derived form |
| 20 | SQLite: bare column in an aggregate query with `min` / `max` | open |
| 21 | `ROW` values and row comparison with more than one column outside `IN` | open |
| 22 | Static typing and well-formedness of queries (I5) | open |
| 23 | Mathematical functions: correct rounding, `numeric` scales of PostgreSQL, bit operators | resolved (TODO 2.1, `docs/functions/math.md`); `rand()`/`random()` without seed excluded (nondeterministic) |
| 24 | String functions of each dialect | resolved (TODO 2.2, `docs/functions/strings.md`); Unicode case folding (`upper`, `lower`, `ILIKE` beyond ASCII) open: needs generated case-mapping tables |
