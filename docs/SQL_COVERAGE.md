# SQL query coverage: audit and extension

This document records an audit of the formalisation against the query language
of SQL (queries only: no DDL, no DML), and what was changed as a result. Every
claim below is checked by computation in `src/testing/Test_Audit.v` and
`src/testing/Test_SqlFull.v`, which are part of the build.

## 1. Audit of the existing formalisation

### Inaccurate (results differ from SQL)

| # | Where | Problem | Status |
|---|---|---|---|
| A1 | `Values.v`, `interp_aggregate` | `count(e)` counted NULLs; `sum`/`max` of an empty or all-NULL group were `0`; `avg` divided by the number of rows, NULLs included, and was `0` on an empty group; `max` was `0` if any value was not an integer; no `min` | fixed |
| A2 | `Values.v`, `interp_predicate` | `<`, `<=`, `>`, `>=` were UNKNOWN on strings, `=` and `<>` were UNKNOWN on booleans | fixed |
| A3 | `SqlExt.v`, `eval_sql_query_ext` | joins were folded from the right, so the `ON` condition of a join could not see the earlier joins; the result disagreed with `sql_query_ext_to_sql_query` | fixed |
| A4 | `Sql.v` + `make_groups` | an aggregate query without `GROUP BY` over an empty input returns no row; SQL returns one | open in `Sql.v`, correct in `SqlFull.v` |
| A5 | `Formula.v`, `Sql_In` | `(a, b) [NOT] IN (q)` was UNKNOWN whenever any component is NULL; SQL compares component-wise, so a definite mismatch gives FALSE | fixed (`in_match`) |
| A6 | `Sql.v`, FROM list | items sharing an attribute name are merged silently (`FROM w, w` yields each row twice) | by design (named tuples); documented |

A4 is not fixed in `Sql.v` because the equivalence proof with the algebra
(`SqlAlgebra.v`) depends on the current definition of `make_groups`; see
`docs/OPEN_ISSUES.md`.

### Incomplete (not expressible before)

`DISTINCT`; `UNION`/`INTERSECT`/`EXCEPT` without `ALL`; outer joins; `LATERAL`;
`ORDER BY`, `OFFSET`, `LIMIT`; scalar subqueries and conditions inside
expressions; `CASE`; `FILTER` and `DISTINCT` on aggregates; window functions;
`WITH`; `VALUES`; `IS [NOT] NULL`, `IS [NOT] DISTINCT FROM`, `BETWEEN`, `LIKE`,
`IN (list)`; division, modulo, string functions, `COALESCE`, `NULLIF`, casts; a
numeric type.

## 2. What was added

### `src/data/proof_of_concept/Values.v` (instance, rewritten)

- Values: strings, integers, booleans, and exact numerics (`Value_Q`,
  canonical rationals), each with its NULL. Integers are promoted to numerics.
- Predicates (three-valued): `=`, `<>`, `!=`, `<`, `<=`, `>`, `>=` on every
  type; `is [not] null`, `is [not] true/false/unknown`,
  `is [not] distinct from`, `[not] between`, `[not] like`, `[not] in`,
  `row=`, `row<>`.
- Functions: `+ - * / %`, `abs`, `sign`, `power`, `floor`, `ceil`, `round`,
  `trunc`, `greatest`, `least`, `coalesce`, `nullif`, `case`, `and`, `or`,
  `not`, `||`, `concat`, `length`, `upper`, `lower`, `trim`, `ltrim`, `rtrim`,
  `reverse`, `substring`, `left`, `right`, `replace`, `repeat`, `position`,
  `cast_int`, `cast_numeric`, `cast_string`, `cast_bool`. Every predicate is
  also available as a boolean-valued function.
- Aggregates: `count`, `count(*)`, `sum`, `avg`, `min`, `max`, `bool_and`,
  `every`, `bool_or`, `string_agg`, `group_concat`, `var_pop`, `var_samp`,
  `bit_and`, `bit_or`; the prefix `distinct ` gives `f(DISTINCT e)`.

This is instance-level only: the generic development and the proofs of
`Sql.v` / `SqlAlgebra.v` are untouched and still compile.

### `src/data/sql/SqlFull.v` (new, generic over `Tuple.Rcd`)

A syntax and an executable semantics for the query language:

| Construct | Constructor |
|---|---|
| `SELECT [DISTINCT] ... FROM ... WHERE ... GROUP BY ... HAVING` | `SQ_Select (Select ...)` |
| implicit single group when the block has aggregates and no `GROUP BY` | `G_Fine` |
| `UNION/INTERSECT/EXCEPT [ALL]` | `SQ_Set` |
| `INNER/LEFT/RIGHT/FULL JOIN ... ON`, `CROSS JOIN`, `LATERAL` | `Fr_Join`, `Fr_Cross` |
| table aliases | `Fr_Query q (Ren_List ...)` |
| `ORDER BY ... [ASC/DESC] [NULLS FIRST/LAST]`, `OFFSET`, `LIMIT` | `SQ_Order` |
| scalar subquery, `EXISTS`, `IN`, `op ANY/ALL` | `E_Sub`, `C_Exists`, `C_In`, `C_Quant` |
| `CASE WHEN`, conditions as values, values as conditions | `E_Case`, `E_Cond`, `C_Expr` |
| `agg([DISTINCT] e) FILTER (WHERE c)`, correlated aggregates | `E_Agg` |
| window functions: aggregates, `row_number`, `rank`, `dense_rank`, `ntile`, `lag`, `lead`, `first_value`, `last_value`, `nth_value`; `ROWS` and `GROUPS` frames | `SQ_Window` |
| `WITH name AS (q1) q2` | `SQ_With` |
| `VALUES`, `SELECT` without `FROM` | `SQ_Values`, `SQ_Row` |

`SqlFullFacts.v` proves a few properties of this semantics (an inner join is a
filtered cross product, a left join without unmatched row is an inner join, a
query with no `ORDER BY`/`OFFSET`/`LIMIT` is unchanged by `SQ_Order`, the
connectives obey the laws of the underlying logic, `CASE` evaluates one branch,
an aggregate is the aggregate of its argument over the group).

### Conventions of the semantics

- Tuples are named; set operations require equal sorts.
- Total function: division by zero, an invalid cast, and a scalar subquery
  returning zero or several rows give NULL.
- `ORDER BY`: NULLs are larger than every value unless `NULLS FIRST/LAST` is
  given; ties keep a deterministic order, so `LIMIT` is a function.
- Integer division truncates towards zero; `avg` is an exact numeric.
- `GREATEST`/`LEAST` ignore NULLs.

### Not covered

`RANGE` frames with a numeric
offset and frame exclusion; date/time and floating-point types; collations;
positional or duplicate column names; ordered-set and multi-argument
aggregates; static typing of queries.

## 3. Building

```
cd src
coq_makefile -f _CoqProject -o Makefile
make
```

Checked with Coq 8.15.2.
