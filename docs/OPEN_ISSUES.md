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

**Status: `IN` is fixed (and compared by position since A7, TODO 6.1); the empty-table aggregate is documented, not
changed in `Sql.v` (A4 in `docs/SQL_COVERAGE.md`).** `SqlFull.v` returns the one row of SQL, and is the reference
semantics (option 2 below); the theorems which relate the two (`sql_full_agree3`) cover the grouped blocks with at
least one grouping term.

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

**Status: resolved (TODO 6.1).** `src/data/sql/SqlRelate.v`, `SqlRelateSelect.v`, `SqlRelateAlg.v`: the queries of
`Sql.v` (tables, set operations, selections, grouped blocks, subqueries in formulas) translate to `SqlFull.v` with
the same bag (`sql_full_agree3`), which is also the bag of the relational algebra (`sql_full_alg3`). Not done, and
not planned: an algebra for outer joins, ordering and windows; merging `SqlExt.v` into `SqlFull.v`.

**Former state**: `SqlFull.v` is a new syntax and executable semantics. Its
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

**Status: resolved as decided in I10 (TODO 6.3).** The tuples stay named; the front end names the columns by
position (`src/data/sql/SqlPositional.v`, `src/data/dialects/Positional.v`), and `eval_rename`
(`src/data/sql/SqlRename.v`) proves that the evaluation does not depend on the names.

**Former state**: a tuple is a finite map from attribute names to values.
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

**Status: resolved (TODO 6.2).** Well-formedness (`SqlWellFormed.v`), the sorts of the results (`SqlSorts.v`),
scoping (`SqlScoping.v`, `SqlScopeQuery.v`) and static types per dialect (`Typing.v`, `TypeOf.v`). The block of an
aggregate is the innermost block which binds one of its columns, in `SqlFull.v` and, since A8, in `Sql.v`.

**Former state**: queries have no type system. A comparison between values
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

Since then: the decimal scale (TODO 1.2.1), floating-point numbers and integer ranges (1.2.2, 1.2.3), dates and
times, JSON, regular expressions (1.5, 1.6, 2.4), `ORDER BY` inside aggregates (2.6, `E_AggX`) and the functional
dependencies of declared keys (`group_covered`, 6.2) are modelled. Still open: the value of a bare column in SQLite
(an arbitrary row of the group, TODO 3.10), and Oracle mode has no recorded results of an engine.

Former list of what was open:
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

**Status: every item of this list is done** (the last ones by TODO 1.3 collations, 1.5 dates and times, 1.2.2
floating point, 2.6 ordered-set aggregates and `ORDER BY` inside aggregates).

In the expected order of difficulty; priorities are to be decided:
- (done) recursive CTEs: `SQ_WithRec` iterates the step on the working table (`UNION ALL` appends, `UNION` keeps only new rows and stops on a fixpoint); the number of steps is bounded by `rec_fuel` (1000, as MySQL's `cte_max_recursion_depth`), so a non-terminating recursion returns the rows of the first 1000 steps instead of an error; mutual and multiple recursion are not modelled;
- (done) `GROUPING SETS` / `ROLLUP` / `CUBE` / `GROUPING()`: grouping expressions that a set does not group read as NULL;
- (done) `FETCH FIRST n [PERCENT] ROWS ONLY | WITH TIES` (`SQ_Fetch`): `WITH TIES` is accepted by PostgreSQL and Oracle mode, `PERCENT` (rounded up, computed before the offset) by Oracle mode only;
- (done) `RANGE` window frames with integer offsets (`Frame_Range`): single numeric ORDER BY key, descending order mirrored, NULL keys are peers of each other only; decimal offsets, `INTERVAL` offsets and frame exclusion are not covered;
- date/time types, floating-point numbers, collations;
- ordered-set aggregates (`percentile_cont`, ...), aggregates with several
  arguments, `ORDER BY` inside `string_agg`.

## I8. Build and repository maintenance

**Status: resolved.**

- Resolved: `make` at the top level now generates `src/Makefile` from
  `src/_CoqProject`; the generated `src/CoqMakeFile*` are no longer tracked.
- Resolved: the opam file requires Coq 8.15, as the README says.
- Resolved: a GitHub Actions workflow builds the library and checks the
  examples on every push to `main` and on every pull request.
- Resolved (TODO 6.5): `fresh_attr_is_fresh` is proved and `src/data/proof_of_concept/FreshAttr.v` is in
  `_CoqProject`. The only `Admitted` left is in a scratch file kept out of the build (`src/testing/legacy/`).

## D1. Scope of further engines (TODO 4.11): decision needed from the maintainers

Status: **decided** (by the maintainer's standing instruction to follow the recommendations without further questions): DuckDB first, then CockroachDB; ClickHouse, Snowflake and BigQuery stay out of scope; Oracle Database and SQL Server are deferred. Tracked as TODO 8.7.

| Engine | Source open? | Distance from the current dialects | Cost of a dialect | Recommendation |
|---|---|---|---|---|
| DuckDB | yes (MIT) | PostgreSQL-like grammar; its own types (`LIST`, `STRUCT`, `MAP`), `QUALIFY`, `GROUP BY ALL`, `ASOF` joins, lambdas | medium: a `vsem` derived from PostgreSQL, plus nested types | **add first**: open source, active test suite in sqllogictest format, which `slt2coq.py` already reads |
| CockroachDB | yes (source available) | PostgreSQL wire and grammar, serializable-only, its own `INT` = 8 bytes and decimal rules | small: PostgreSQL with type differences | add second (logic tests are sqllogictest-like) |
| ClickHouse | yes (Apache 2) | far: no three-valued logic by default (`join_use_nulls`), `Nullable` types, array functions, `FINAL` | large | exclude for now: its default NULL handling departs from the standard core of the model |
| Oracle Database | no | the OceanBase Oracle mode covers its documented `SELECT` | medium, from documentation only | defer: the Oracle mode is the documented subset; a separate dialect adds no source evidence |
| SQL Server | no | `TOP`, `CROSS/OUTER APPLY` (already modelled), `+` on strings, collations by default case-insensitive | medium, documentation only | defer |
| Snowflake, BigQuery | no (services) | `QUALIFY`, semi-structured types, `SAFE_` functions; results not reproducible locally | large, documentation only | exclude: no engine to validate against (Phase 5 needs one) |

Questions for the maintainers: (1) agree to DuckDB then CockroachDB as the next dialects? (2) keep ClickHouse,
Snowflake and BigQuery out of scope? (3) is Oracle Database / SQL Server worth a documentation-only dialect?

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

## I10 — Scope of TODO 6.3 (positional semantics) — RESOLVED

TODO 6.3 asks to migrate the tuples of `SqlFull.v` to positions and keep a named view for the old lemmas. What exists
(`src/data/sql/SqlPositional.v`) is the converse: a positional semantics of a smaller language (tables, selections,
`SELECT *` over products, `UNION ALL`) compiled to the named semantics, with the theorem that the compiled rows read by
position are the positional rows (`positional_rows`). A real migration changes the tuple type of `SqlFull.v`
(`Tuple.Rcd` has sets of labels, which cannot hold two columns of one name), so that every definition and proof
built on it (congruence, sorts, scoping, refinement, the relation to `Sql.v`) has to be redone. Question for the
maintainers: is the compiled positional view an acceptable resolution, should it be extended to the whole `SqlFull.v`
syntax (subqueries, grouping, joins, windows, `WITH`), or is the full migration required?

Decision (maintainer): keep the tuples of `SqlFull.v` named and prove, for the whole syntax, that the evaluation does
not depend on the names. Done in `src/data/sql/SqlRename.v` (`eval_rename`): the rows of a query renamed by an
bijection of the attributes (which preserves their types), over the renamed database, are the renamed rows of the query. The
compiled positional language of `SqlPositional.v` stays as the example of the front end's naming.

Related, for TODO 6.1: `IN (subquery)` and grouped blocks inside formulas needed two fixes of `Sql.v` (A7, A8 in
`docs/SQL_COVERAGE.md`); both are fixed and the relation covers them (`sql_full_agree3`).

## I11 — The order in which a stored table is read depends on the names of its columns — OPEN

Found by iteration 4 (`docs/ITERATIONS.md`). A stored table is a bag (`instance : relname -> bagT`), and
`eval_squery` reads its rows with `Febag.elements`, in the order of the tuples; the order of the tuples of the
instance compares the values in the order of the attributes, which is the order of their types and names. So the
same rows stored under other column names may be read in another order, and a query whose result depends on the
order of the rows (`LIMIT` without `ORDER BY`, ties of an `ORDER BY`, `string_agg` without order) may give another
result. Consequences:
- `eval_rename` needs the hypothesis that the rows of each table are related one by one in the same order
  (`Hinst`); `src/testing/Test_Rename.v` uses a table for which the two orders coincide.
- The conformance harness compares such results as bags or with the allowed results of TODO 3.10, so it is not
  affected.

Options: (a) keep it, documented (the order of an unordered table is implementation-defined in SQL as well); (b)
store tables as lists (insertion order, as the engines without a clustered key do), which changes
`instance` in `SqlFull.v` and every statement which mentions `Febag.elements`; (c) prove the bag version of
`eval_rename` for the queries whose result does not depend on the order of the stored rows. Tracked as TODO 8.10.

