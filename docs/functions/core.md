# Core operators, predicates, casts and Phase 1 functions

This file documents, with their sources, the entries of the function, predicate and aggregate tables that
the other files of `docs/functions/` do not cover. These are the operators and casts of Phase 1, the
basic functions that the dialects had before Phase 2, and the internal names which the translator
produces for syntax. `tools/functions/check_provenance.py` checks that every entry of the tables is
documented somewhere in this directory.

## Arithmetic and logic (Phase 1.2, 1.4)

| Names | Meaning | Sources / notes |
|---|---|---|
| `+` `plus`, `-` `minus`, `*` `mult`, `/` `div`, `%` `mod`, `opp` `neg` | arithmetic. `plus`, `minus`, `mult`, `div`, `mod`, `opp` and `neg` are the internal names for the operators and for unary minus. | integer ranges (PostgreSQL `int.c`, MySQL `Item_func_plus`); decimal scales (`numeric.c` `select_div_scale`, MySQL `div_precision_increment`); IEEE doubles (`IEEE.v`) |
| `and`, `or`, `not`, `xor` | the connectives as functions (MySQL truth values 1/0/NULL) | three-valued logic, `Bool3.v` |
| `&`, `\|`, `^`, `~`, `<<`, `>>`, `#` | bit operators | math.md |
| `true`, `false`, `unknown` | the constant predicates | |
| `||` | concatenation (PostgreSQL, SQLite, Oracle), logical or (MySQL unless `PIPES_AS_CONCAT`) | `sql_mode`, TODO 1.10 |

## Comparisons and predicates (Phase 1, TODO 2.3)

| Names | Meaning | Sources / notes |
|---|---|---|
| `=` `<>` `!=` `<` `<=` `>` `>=` | comparisons in the order of each dialect: types, collations, temporal, JSON, arrays | TODO 1.3, 1.5, 1.6, 2.8 |
| `row=` `row<>` | row comparison `(a, b) = (c, d)` | SQL standard 8.2 |
| `row<` `row<=` `row>` `row>=` | row ordering: the first pair which is not equal decides; a NULL before the decision is UNKNOWN | SQL standard 8.2; TODO 3.7 |
| `row is null`, `row is not null` | `(a, b) IS [NOT] NULL`: all NULL, none NULL | SQL standard 8.8 |
| `overlaps` | PostgreSQL `(s1, e1) OVERLAPS (s2, e2)` (an end may be an interval) | manual 9.9, `overlaps_timestamp`; TODO 3.7 |
| `is null`, `is not null`, `is true`, `is not true`, `is false`, `is not false`, `is unknown`, `is not unknown` | the `IS` predicates | SQL standard 8.8, 8.12 |
| `is`, `is not` | SQLite's NULL-safe equality | SQLite `lang_expr.html` |
| `is distinct from`, `is not distinct from` | NULL-safe comparison (PostgreSQL, SQLite) | conditional.md |
| `between`, `not between`, `between symmetric`, `not between symmetric` | ranges | conditional.md |
| `in`, `not in` | membership in a list | conditional.md |
| `like`, `not like` | `LIKE` with the dialect's default escape | strings.md |
| `like_escape`, `not like_escape`, `ilike`, `not ilike`, `ilike_escape`, `not ilike_escape` | `LIKE … ESCAPE`, `ILIKE`: internal names | strings.md |
| `not similar to`, `not regexp_like` | the negated forms of `SIMILAR TO` and `REGEXP_LIKE` | regex.md |

## Casts (Phase 1.9)

| Names | Target type | Notes |
|---|---|---|
| `cast_int`, `cast_smallint`, `cast_bigint`, `cast_unsigned` | integers (range checks per dialect, MySQL `UNSIGNED`) | Phase 1.2.3 |
| `cast_numeric`, `cast_decimal` | decimals with precision and scale | Phase 1.2.1 |
| `cast_float4`, `cast_float8`, `cast_double`, `cast_real` | binary floating point | Phase 1.2.2 |
| `cast_string` | text (each dialect's text of each type) | Phase 1.9 |
| `cast_bool` | boolean (PostgreSQL) | Phase 1.4 |
| `cast_date`, `cast_time`, `cast_timestamp`, `cast_timestamptz`, `cast_datetime`, `cast_interval` | temporal types | Phase 1.5 |
| `lit_datetime`, `lit_time` | the typed literals `TIMESTAMP '...'` and `TIME '...'` of the MySQL family: an invalid literal is an error (`ER_WRONG_VALUE`), the fields of a `TIMESTAMP` are separated by any punctuation | MySQL manual, "Date and Time Literals"; TiDB `tests/integrationtest/r/expression/misc.result` |
| `cast_json`, `cast_jsonb` | JSON | Phase 1.6 |
| `collate` | `x COLLATE name` | Phase 1.3 |

## Basic string functions (before Phase 2)

| Names | Dialects | Notes |
|---|---|---|
| `concat` | all | PostgreSQL and MySQL `CONCAT`; NULL-skipping or not per dialect |
| `char_length`, `length`, `upper`, `lower`, `trim`, `ltrim`, `rtrim`, `reverse`, `repeat`, `replace`, `left`, `right` | per their manuals | MySQL `LENGTH` counts bytes, the others count characters (strings.md) |
| `substring`, `substr`, `mid` | all; `mid` MySQL | 1-based, negative starts per dialect |
| `typeof` | SQLite | the storage class (`typeofFunc`) |
| `trim_both`, `trim_leading`, `trim_trailing` | internal names of `TRIM(BOTH/LEADING/TRAILING … FROM …)` | strings.md |
| `substring_regex` | internal name of PostgreSQL `substring(s from pattern)` | regex.md |

## Dates (Phase 1.5)

| Names | Dialects | Notes |
|---|---|---|
| `current_date`, `current_time`, `current_timestamp`, `localtimestamp`, `curdate`, `curtime`, `systimestamp`, `statement_timestamp`, `transaction_timestamp`, `utc_date`, `utc_time`, `utc_timestamp` | per dialect | the statement time, 2026-01-01 12:00 UTC (datetime.md) |
| `year`, `quarter`, `month`, `week`, `weekday`, `day`, `dayofmonth`, `dayofweek`, `dayofyear`, `hour`, `minute`, `second`, `microsecond` | MySQL family | `Item_func_year` …, `calc_week` (mode 0 by default) |
| `interval_index` | internal name of MySQL `INTERVAL(n, n1, …)` | conditional.md |

## JSON (Phase 1.6)

| Names | Dialects | Notes |
|---|---|---|
| `json`, `json_array`, `json_object`, `json_extract`, `json_type`, `json_valid`, `json_array_length` | SQLite (`json1`), MySQL | `->`, `->>` also. The paths of the MySQL family (`json_path.cc`) have `.*`, `[*]`, `[m to n]`, `last`, `last-n` and `**`; `json_extract` with such a path or with several paths gives the array of the values found; `[0]` and `[last]` apply to a value which is not an array. SQLite has none of them |
| `json_contains`, `json_keys`, `json_length`, `json_unquote` | MySQL | `Item_func_json_*` |
| `json_build_array`, `json_build_object`, `jsonb_build_array`, `jsonb_build_object`, `json_typeof`, `jsonb_typeof`, `jsonb_array_length`, `to_json`, `to_jsonb`, `#>>` | PostgreSQL | manual 9.16 |

## Internal names of other constructs

| Name | Construct | Notes |
|---|---|---|
| `subscript`, `slice` | PostgreSQL `a[i]`, `a[i:j]` | json_arrays.md |
| `max_scalar`, `min_scalar` | SQLite scalar `max(a, b, …)`, `min(…)` | conditional.md |
| `count_distinct2` | MySQL `COUNT(DISTINCT a, b)` | aggregates.md |
| `group_concat_sep`, `string_agg_sep` | `GROUP_CONCAT(… SEPARATOR s)`, `string_agg(x, s)` | `E_AggX` |
