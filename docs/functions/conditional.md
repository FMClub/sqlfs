# Comparison and conditional functions (TODO 2.3)

Status: **M** modelled, **—** the engine has no such construct. Tests: `src/testing/Test_Cond.v`,
`Test_Truth.v`, `Test_Audit.v`.

| Construct | PostgreSQL | MySQL family | SQLite | Oracle mode | Notes |
|---|---|---|---|---|---|
| `x IN (list)`, `NOT IN` | M | M | M | M | three-valued: a NULL in the list makes a miss UNKNOWN (`1 NOT IN (2, NULL)` is UNKNOWN). Comparisons follow each dialect's conversions. |
| `BETWEEN`, `NOT BETWEEN` | M | M | M | M | `lo <= x AND x <= hi` |
| `BETWEEN SYMMETRIC` | M | — | — | — | the bounds in either order |
| `IS [NOT] DISTINCT FROM` | M | — (`<=>`) | M (also `IS` / `IS NOT`) | — | NULL-safe equality |
| `<=>` | — | M | — | — | |
| `GREATEST`, `LEAST` | M (NULLs ignored) | M (NULL if any argument is NULL) | — (scalar `max`/`min`) | M (NULL if any) | MySQL compares in the common type of the arguments (number, string with the session collation, temporal) |
| scalar `max(a, b, …)`, `min` | — | — | M (NULL if any; the order of `ORDER BY` between types) | — | the translator tells them from the aggregates by their arity |
| `COALESCE`, `NULLIF` | M | M | M | M (`''` is NULL) | |
| `IFNULL` / `NVL` | — | M (`IFNULL`) | M (`ifnull`) | M (`NVL`) | |
| `NVL2` | — | — | — | M | |
| `IF(c, a, b)` / `IIF` | — | M (`IF`) | M (`iif`) | — | |
| `DECODE(e, s1, r1, …, d)` | — | — | — | M | two NULLs match |
| `CASE` | M | M | M | M | core `E_Case` |
| `ISNULL(x)` | — | M | — | — | 1 or 0 |
| `INTERVAL(n, n1, …)` | — | M | — | — | the number of `ni <= n`; -1 when `n` is NULL |
| `num_nulls`, `num_nonnulls` | M | — | — | — | |
| `likely`, `unlikely`, `likelihood` | — | — | M | — | the value of the argument |

## Known differences

- The result type of `COALESCE`, `CASE`, `GREATEST` is the type of the selected argument. The engines
  convert it to the common type of all the arguments: for example, MySQL `COALESCE(1, 'a')` is the
  string `'1'`. This matters only for the column type, and the printed value is the same. Static typing is
  TODO 1.9 / 6.2.
- MySQL `GREATEST(2, '10')` compares as numbers and returns the number 10. The model returns the
  argument `'10'`, whose text is the same.
