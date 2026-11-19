# Aggregates (TODO 2.5)

Status: **M** modelled, **X** excluded (with the reason), **—** the engine has no such aggregate. Code: `src/data/dialects/Aggregates.v`
and the aggregate tables of each dialect (`Values.v`, `MySQL.v`, `SQLite.v`, `OceanBase.v`). Tests:
`src/testing/Test_Aggregates.v` and the aggregate tests of `Test_Decimal.v`, `Test_Float.v` and `Test_SqlFull.v`.

| Aggregate | PostgreSQL | MySQL family | SQLite | Oracle mode | Result type / notes |
|---|---|---|---|---|---|
| `count`, `count(*)`, `count(distinct x)` | M | M | M | M | |
| `count(distinct a, b)` | — | M | — | — | pairs without NULL |
| `sum` | M (`sum(int4)` is `bigint`, `sum(int8)` is `numeric`) | M (`DECIMAL` of integers, `DOUBLE` of doubles) | M (integer overflow is an error; `total` is `REAL`) | M | Phase 1.2 |
| `avg` | M (`numeric` with `select_div_scale`) | M (scale + `div_precision_increment`) | M (`REAL`) | M | Phase 1.2 |
| `min`, `max` | M | M | M | M | the order of each dialect, including collations |
| `bit_and`, `bit_or`, `bit_xor` | M (NULL on the empty group) | M (`BIGINT UNSIGNED`; empty: all ones for `bit_and`, 0 for the others) | — | — | `Item_sum_bit` |
| `bool_and`, `bool_or`, `every` | M | — | — | — | |
| `var_pop`, `var_samp`, `variance` | M (`numeric` of integers and `numeric` values, `select_div_scale` scale; `double` of doubles; `variance` is the sample variance) | M (`DOUBLE`; `VARIANCE` is the population variance) | — | M (exact) | `numeric_stddev_internal`; `Item_sum_variance` |
| `stddev_pop`, `stddev_samp`, `stddev`, `std` | M (`stddev` is the sample one; `numeric` square root at the scale of the variance) | M (`STD`, `STDDEV` are the population ones) | — | — | |
| `covar_pop`, `covar_samp`, `corr`, `regr_*` | M (`double precision`) | — | — | X (NUMBER precision: Phase 4) | computed exactly, rounded once |
| `any_value` | M (PostgreSQL 16: the first non-NULL value, which is one of the allowed results) | X (in MySQL it is a function marking a bare column: TODO 1.x bare columns) | — | — | |
| `group_concat`, `string_agg`, `listagg` with `ORDER BY` and a separator | M | M (`group_concat_max_len`) | M | M | `E_AggX` |
| `json_agg`, `jsonb_agg` | M (text `[a, b]`) | — | — | — | |
| `json_object_agg`, `jsonb_object_agg` | M (text `{ "k" : v }`) | — | — | — | |
| `JSON_ARRAYAGG`, `JSON_OBJECTAGG` | — | M (a NULL key is an error) | — | — | |
| `array_agg` | X (arrays: TODO 2.8) | — | — | — | |
| `percentile_*`, `mode`, `median` | → TODO 2.6 | | | | |
| `approx_count_distinct` | — | X (TiDB: approximate by definition) | — | X | the result is not specified exactly |
| `FIRST`/`LAST` with `KEEP (DENSE_RANK …)` | — | — | — | X (syntax not in the core: Phase 3) | |

## Empty groups

An empty group gives the following results:

- `count` is 0.
- `bit_and`, `bit_or` and `bit_xor` give MySQL's constants (all ones for `bit_and`, 0 for the others) and NULL in PostgreSQL.
- `JSON_ARRAYAGG` and `json_agg` are NULL.
- The other aggregates are NULL.

## Known differences

- The variance in double precision is computed exactly and rounded once. MySQL uses a running
  recurrence in doubles (`variance_fp_recurrence_next`) and PostgreSQL uses the Youngs–Cramer algorithm, so
  the last digit can differ.
- The statistics of Oracle mode (`VARIANCE` …) are exact rationals. Oracle's `NUMBER` precision (38–40
  significant digits) is Phase 4.
