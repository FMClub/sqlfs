# To-do list for a complete formal semantics of SQL queries

This is the work plan; `docs/CHECKLIST.md` says what is done. Each item says **what** to do, **where**
(files), **how** (design), **sources** (where the truth is established), **done when** (acceptance, checked by the
build), and **depends on**. Items are in the order in which they should be done. Every item ends with: update
`docs/CHECKLIST.md` and `docs/OPEN_ISSUES.md` I9, one pull request, a comment on PR #1.

Rules for all items (from the project's standing instructions):
- Do not guess a dialect's behaviour: read its source (`MariaDB/server`, `pingcap/tidb`, `oceanbase/oceanbase`, `postgres/postgres`,
  `mysql/mysql-server`, `sqlite/sqlite`, Percona and PolarDB documentation) and cite the file or page in the Coq comment and in `docs/DIALECTS.md`.
- A behaviour which cannot be established is recorded as an open question in a pull request, marked unresolved, never approximated silently.
- Repository artefacts are in English.
- Direction problems go to `docs/OPEN_ISSUES.md`; detail problems are fixed directly.

---------------------------------------------------------------------------------------------------------

## Phase 1. Foundations of the value model

These change the type of values or of results, so they come first: every function of Phase 2 depends on them.

### 1.1 Results with errors (I3, ledger 14) — DONE
- **What**: a query may fail (division by zero in PostgreSQL, `CAST('a' AS INT)` in strict modes, integer overflow, a scalar
  subquery which returns two rows, `cte_max_recursion_depth` exceeded). Today these are NULL.
- **How**: add to the `dialect` record an error value, `error : error_kind -> value`, and `is_error : value -> bool`; make `E_Fun`, `E_Agg`, `E_Case`, `E_Cond`,
  `C_Pred` propagate an error value strictly (an error argument gives an error, except where the engine short-circuits: `CASE`, `AND`/`OR`, `COALESCE`
  evaluate lazily in PostgreSQL and MySQL; record per construct whether evaluation is lazy). Add `eval_query_result : ... -> result` where
  `result = Rows (list tuple) | Error error_kind`. Conditions: extend `bool3` handling with an error flag or evaluate conditions to `option bool3`.
  Make the choice per dialect through a flag `errors_on_div_zero` etc., so MySQL (NULL plus warning in `SELECT`) and PostgreSQL (error) differ.
- **Sources**: PostgreSQL `src/backend/utils/adt/*.c` (`ereport(ERROR, ...)`); MySQL `sql_mode` documentation (`ERROR_FOR_DIVISION_BY_ZERO`, strict mode only affects DML);
  MariaDB/TiDB/OceanBase source for `division by zero`, `Truncated incorrect ... value`; SQLite never raises on arithmetic.
- **Files**: `SqlFull.v` (`dialect`, `eval_*`), `Dialects.v`, all dialect files, `SqlFullFacts.v` (lemmas change), tests.
- **Done when**: tests show `SELECT 1/0` is an error in PostgreSQL and Oracle mode, NULL in MySQL, MariaDB, TiDB (default), SQLite; an error in an unused `CASE` branch does not
  surface; a query with an error in a `WHERE` row that is filtered out earlier by another condition follows the dialect's evaluation order (documented as unspecified where it is).
- **Depends on**: nothing; do first because all later items return errors.

### 1.2 Numeric tower
Split `value` into exact decimal with scale, binary floating point, and fixed-width integers, per dialect.
- **1.2.1 Decimal scale and precision. — DONE** (`Value_D (q, f, s)`: exact value, digits held, scale;
  PostgreSQL `numeric` rules with `select_div_scale`; MySQL-family `decimal.c` rules, 9-digit units, quotient truncated and
  displayed with the dividend's scale plus `div_precision_increment`; literals keep their scale, are `REAL` in SQLite and
  scale-less `NUMBER` in Oracle mode; `DECIMAL(p,s)` columns store values rounded to `s`; tests `Test_Decimal.v`;
  OceanBase cases `length(0.00)` and `4/3 = 1.333333333` now pass. Not covered: the caps of precision (65 digits in MySQL,
  1000 in PostgreSQL) and overflow, which come with 1.2.3.)
  Original plan: Add `Value_D : option (Z * nat)` (unscaled value and scale) or equivalent; reprove the ordered-type instance `OVal`
  (`value_compare`, equality is by numeric value, scale is not part of identity for `GROUP BY`/`DISTINCT` but is for display and `length`). Rules: `+`, `-` scale = max; `*` scale = sum;
  `/` scale per dialect (MySQL/MariaDB/TiDB/Percona/PolarDB: scale of dividend + `div_precision_increment`; OceanBase: see source `ob_number`/`ObNumber` internal precision, which explains `4/3 = 1.333333333`;
  PostgreSQL: `numeric` division scale rule `select_div_scale`; Oracle mode: 38 significant digits); `ROUND`, `TRUNCATE`, `CAST(.. AS DECIMAL(p,s))` with overflow and rounding rule; `SUM`/`AVG` scale rules.
  *Done when*: the 6 remaining OceanBase conformance cases pass (`length(0.00)` is 4; `4/3 = 1.333333333`), `SELECT 1.0 = 1.00` is true, `SELECT 1.50 || ''` is `1.50` in PostgreSQL.
- **1.2.2 Floating point. — DONE** (`IEEE.v`: rounding of a rational to binary64/binary32, ties to even,
  overflow, subnormals; the shortest round-trip text of PostgreSQL (`d2s.c`) and of the MySQL family (`my_gcvt`), SQLite's
  `%!.15g`; `Value_F`; PostgreSQL `float8`/`float4` arithmetic with its errors, NaN and infinities, `rint`, casts to and
  from `numeric`; MySQL doubles, strings converted to doubles, sums rounded at each addition, binary32 `FLOAT`; SQLite
  `REAL`; tests `Test_Float.v`. Open: Oracle `BINARY_DOUBLE`, `extra_float_digits` values other than the default,
  `REAL_AS_FLOAT`, trigonometric and logarithmic functions (with Phase 2.1).)
  Original plan: Add `Value_F` with IEEE 754 binary64/binary32 semantics (round to nearest even, `NaN`, `±Infinity`, `-0`); implement it over `Z` mantissa/exponent
  (a verified soft-float, or use the Flocq library if it is acceptable as a dependency; decide and record). Rules per dialect: PostgreSQL `float4`/`float8` text output (shortest round-trip, `extra_float_digits`),
  `NaN` sorts greatest and equals itself; MySQL `DOUBLE`, `FLOAT`, `REAL` (`REAL_AS_FLOAT` mode), no `NaN` stored; SQLite `REAL` (no `NaN`, becomes NULL); Oracle `BINARY_DOUBLE` vs `NUMBER`.
  *Done when*: `0.1+0.2` is `0.30000000000000004` where the engine gives it; sqllogictest `R` columns match without the `%.3f` rounding being relied on for non-trivial cases.
- **1.2.3 Integer types and overflow. — DONE** (`Value_I (z, w)`: PostgreSQL `smallint`/`integer` and MySQL
  `BIGINT UNSIGNED`; `Value_Z` is the 64-bit `bigint`. PostgreSQL: the result has the wider type, overflow is an error,
  literals are `integer`, `bigint` or `numeric` by size, `CAST` to each width; MySQL: `BIGINT` arithmetic, unsigned when
  an operand is unsigned, overflow is an error, literals above 2^63 - 1 are unsigned and above 2^64 - 1 decimal,
  `CAST(... AS UNSIGNED)` modulo 2^64; SQLite: an overflow gives a `REAL`, `sum` fails with `integer overflow`;
  translator: PostgreSQL integer columns and MySQL unsigned columns; tests `Test_Integer.v`. Open:
  `NO_UNSIGNED_SUBTRACTION`, `TINYINT`/`MEDIUMINT` column ranges on insertion (DML), Oracle `NUMBER` precision.)
  Original plan: Types `TINYINT`..`BIGINT`, `UNSIGNED`, PostgreSQL `int2/int4/int8`, SQLite 64-bit with float promotion on overflow, Oracle `NUMBER`.
  Rules: arithmetic overflow is an error (MySQL: `BIGINT value is out of range`), `BIGINT UNSIGNED` minus gives error unless `NO_UNSIGNED_SUBTRACTION`, `abs(INT_MIN)`, literal typing (smallest type that fits).
  *Done when*: `SELECT 9223372036854775807 + 1` is an error in PostgreSQL/MySQL and a float in SQLite.
- **1.2.4 Numeric text. — DONE with 1.2.1 and 1.2.2** (decimals print their scale, floats the text of each engine,
  integers their digits; open: the Oracle-mode text of a `NUMBER` below 1 (`.5` in Oracle Database), which the
  OceanBase formatter (`ObNumber::format`, no trailing zeros in Oracle mode) does not establish either way.)
  Original plan: Output of numbers as text for `CAST(.. AS CHAR)` and concatenation per dialect (`1e+20`, `1.0E10`, trailing zeros).
- **Depends on**: 1.1.

### 1.3 Strings: collations, charsets, padding — DONE (see the status below)

Status: `Collation.v` with weights generated by `tools/collation/gen_collations.py` from the engines' own
tables (`utf8mb4_general_ci`, `utf8mb4_0900_ai_ci` (UCA 9.0.0), `utf8mb4_unicode_520_ci`, `utf8mb4_unicode_ci`,
`utf8mb4_bin`, SQLite `BINARY`/`NOCASE`/`RTRIM`, PostgreSQL `C`), UTF-8 decoding, expansions (`ß` = `ss`),
`PAD SPACE`/`NO PAD`, `LIKE`/`LOCATE`/`INSTR` by characters and collation, `COLLATE` (`Value_C`) with the
precedence of an explicit collation and `Illegal mix of collations`, `CHAR(n)` columns of MySQL without their
trailing spaces; tests `Test_Collation.v`. Open (recorded in `docs/OPEN_ISSUES.md`): MariaDB's
`utf8mb4_uca1400_ai_ci` is approximated by UCA 9.0.0 (its tables are generated at build time and are not in the
source); weights above U+02FF use the code point (UCA implicit weights); column-level collations and the
coercibility of columns vs. literals; PostgreSQL ICU and libc collations; PostgreSQL `char(n)`; charsets other
than UTF-8; `BINARY` strings and `bytea`.

- **What**: model a collation as a record: comparison function, sort key function, `PAD SPACE`/`NO PAD`, case and accent sensitivity, and the charset's validity rules.
  Today: byte-wise, case-insensitive with optional `PAD SPACE` (`mysql_vs`).
- **How**: `collation := { coll_name; coll_cmp : string -> string -> comparison; coll_key : string -> string; coll_pad : bool }`; instances: `binary`, `utf8mb4_bin`, `utf8mb4_general_ci`,
  `utf8mb4_0900_ai_ci`, `utf8mb4_0900_as_cs`, `utf8mb4_unicode_ci`, `utf8mb4_uca1400_ai_ci` (MariaDB), `latin1_swedish_ci`, SQLite `BINARY`/`NOCASE`/`RTRIM`, PostgreSQL `C`/`en_US.utf8` (glibc, ICU: document that
  these depend on the OS and cannot be fully specified; choose `C` and ICU root collation as the two models). Implement accent folding via a table generated from the engine's collation data
  (`strings/ctype-uca*.c`, `ctype-utf8.c` in MariaDB; MySQL `strings/ctype-uca.cc`; TiDB `pkg/util/collate/*`; OceanBase `deps/oblib/src/lib/charset/*`).
  Add `COLLATE` as an expression and the collation precedence rules (coercibility: explicit > column > literal; "illegal mix of collations" error).
  Strings become `list` of code points or bytes with an explicit charset; `LENGTH` (bytes) vs `CHAR_LENGTH` (characters); `UPPER`/`LOWER` per charset.
- **Done when**: `'a' = 'A'`, `'a' = 'á'`, `'a' = 'a '` give the engine's answers for each default collation (matrix in `docs/DIALECTS.md` verified against the engine source), `ORDER BY` of a mixed string set
  matches `utf8mb4_0900_ai_ci` weights for Latin and common scripts.
- **Depends on**: 1.1 (illegal mix is an error).

### 1.4 Booleans and truth values per dialect — DONE (dialect field `truth_error`: PostgreSQL accepts only a boolean
or a boolean literal string as a condition, other values are type errors; MySQL and SQLite read the numeric
prefix; Oracle mode has no condition values (`F_Cond_Value`); tests `Test_Truth.v`. Open: PostgreSQL's untyped
`NULL` vs a typed NULL is not distinguished, so every NULL is accepted as a condition.)
- **What**: PostgreSQL `boolean` type, `IS TRUE`; MySQL/MariaDB/TiDB: `TRUE` is `1`, comparisons yield 0/1/NULL; SQLite same; Oracle mode: no boolean type in SQL, conditions cannot be selected.
- **How**: finish `truth_of_value`/`value_of_truth` for every dialect (strings and numbers as conditions: MySQL `WHERE 'abc'` is false with a warning, `WHERE '1abc'` true; PostgreSQL error;
  SQLite numeric prefix rules); `F_Cond_Value` per dialect.
- **Done when**: a table of `WHERE <non-boolean>` behaviours matches each engine.

### 1.5 Dates, times, intervals — DONE (see the status below)

Status: `Temporal.v` (proleptic Gregorian calendar, ISO weeks, texts, parsing, `DATE_FORMAT`/`to_char`
patterns, the time of the statement as a parameter), `Value_T`/`Value_V`; PostgreSQL date/timestamp/interval
arithmetic, `EXTRACT`/`date_part`/`date_trunc`/`to_char`/`make_date`/casts with errors; MySQL family dates as numbers
(`YYYYMMDD`), `+ INTERVAL`, `DATE_ADD`/`DATEDIFF`/`TIMESTAMPDIFF`/`YEAR`..`MICROSECOND`/`WEEK` (mode 0)/`DATE_FORMAT`/
`LAST_DAY`/`TO_DAYS`/`UNIX_TIMESTAMP`/casts (NULL on invalid); SQLite `date`/`time`/`datetime`/`julianday`/`unixepoch`/
`strftime` with modifiers (no clamping of months); Oracle mode `DATE` with time, `date +/- n`, `date - date`, `TO_DATE`
(any separator), `TO_CHAR`, `NLS_DATE_FORMAT` `DD-MON-RR`, `ADD_MONTHS`, `LAST_DAY`, `MONTHS_BETWEEN`, `EXTRACT`; the
translator reads temporal literals, `INTERVAL n unit` and temporal columns; tests `Test_Date.v`. Open: time zones
other than UTC and `AT TIME ZONE`, `WEEK` modes other than 0, `STR_TO_DATE`, PostgreSQL `age` and `justify_*`, zero
dates of MySQL (`NO_ZERO_DATE` concerns insertion), leap seconds, years outside 1..9999 for MySQL, the `RR` year rule.

- **What**: types `DATE`, `TIME`, `DATETIME`/`TIMESTAMP` (with and without time zone), `YEAR`, `INTERVAL`; calendar (proleptic Gregorian), leap years, ranges per dialect
  (MySQL `1000-01-01`..`9999-12-31` for `DATETIME`, `1970`..`2038` for `TIMESTAMP`; PostgreSQL 4713 BC..294276 AD), fractional seconds precision (0..6), zero dates and `NO_ZERO_DATE`.
- **How**: `Value_Date`, `Value_Time`, `Value_Timestamp` over `Z` (days or microseconds); parsing of literals and implicit string conversion; arithmetic (`date + interval`, month-end rules: `Jan 31 + 1 month`);
  `EXTRACT`, `DATE_TRUNC`/`DATE_FORMAT`/`TO_CHAR`/`STR_TO_DATE`/`strftime` (SQLite: dates are strings/numbers: implement the SQLite date functions on text and Julian day numbers); time zone as a parameter (`time_zone`, `TimeZone`),
  `CURRENT_*` and `NOW()` as a query-level constant (statement start) given in the environment.
- **Sources**: PostgreSQL `src/backend/utils/adt/datetime.c`, `timestamp.c`; MySQL/MariaDB `sql/sql_time.cc`, `sql/item_timefunc.cc`; TiDB `pkg/types/time.go`; SQLite `src/date.c`; OceanBase `deps/oblib/src/lib/timezone`.
- **Done when**: the `date`/`time` families of sqllogictest `test/evidence` and the OceanBase `mysql_test` date files run; every date function of Phase 2.7 has a value-level spec.
- **Depends on**: 1.1, 1.2.

### 1.6 JSON — DONE (see the status below)

Status: `Json.v` (values, RFC 8259 parsing, normalization of objects as MySQL and `jsonb` do it, texts, the
path language of MySQL and SQLite with negative indices, containment); `Value_J`; PostgreSQL `json` (text kept) and
`jsonb`, `->`, `->>`, `#>`, `#>>`, `@>`, `<@`, `?`, `jsonb_typeof`, `jsonb_array_length`, `jsonb_build_object/array`,
`to_jsonb`; MySQL `JSON_EXTRACT`, `->`, `->>`, `JSON_UNQUOTE`, `JSON_OBJECT`, `JSON_ARRAY`, `JSON_QUOTE`, `JSON_VALID`,
`JSON_TYPE`, `JSON_LENGTH`, `JSON_KEYS`, `JSON_CONTAINS`, comparison of JSON scalars with SQL values; SQLite `json`,
`json_extract`, `->`, `->>`, `json_array`, `json_object`, `json_type`, `json_valid`, `json_array_length`; tests
`Test_Json.v`. Open: wildcards in paths, `JSON_SET`/`INSERT`/`REPLACE`/`REMOVE`, the JSON aggregates, `JSON_TABLE` and
`json_each` (Phase 3.4), SQL/JSON path of PostgreSQL (`jsonb_path_query`), SQLite's JSON subtype, the JSON functions
of Oracle mode (`JSON_VALUE`, `JSON_QUERY`), the order of JSON values of different types.

- **What**: a JSON value type (`Value_Json`), with the three semantics: MySQL/MariaDB/TiDB/OceanBase (binary JSON, ordering across types, `JSON_*` functions, paths `$.a[1]`), PostgreSQL (`json` text and `jsonb`, operators `->`, `->>`, `#>`, `@>`, `?`, SQL/JSON path
  `jsonb_path_query`), SQLite (`json1`: JSON as text, `json_extract`, `->`, `->>`, `json_each`, `json_tree`).
- **How**: an abstract syntax of JSON, parsing and printing per dialect (key order, duplicate keys, number formatting), path language interpreters (MySQL path, SQL/JSON path, SQLite path), comparison and ordering rules,
  `JSON_TABLE`/`json_each`/`jsonb_array_elements` as table functions (Phase 3.4).
- **Sources**: MySQL `sql/json_dom.cc`, `json_path.cc`; PostgreSQL `src/backend/utils/adt/json*.c`, `jsonpath*.c`; SQLite `ext/misc/json1`/`src/json.c`; MariaDB `sql/item_jsonfunc.cc`; TiDB `pkg/types/json_binary.go`.
- **Depends on**: 1.2, 1.3.

### 1.7 Other types — DECIDED (decision record below; the exclusions are proposals for the user to accept)

| Type | Decision | Reason |
|---|---|---|
| PostgreSQL arrays (`ARRAY[...]`, `unnest`, `ANY(array)`, `array_agg`) | to model with Phase 3.4 (table functions) and 2.5 (aggregates) | used by queries (`ANY`, `unnest`) |
| Composite / row types | modelled as row values (Phase 3.7) | |
| MySQL `ENUM` and `SET` | to model with Phase 4.2: an `ENUM` sorts by its index, compares as its text | changes `ORDER BY` results |
| `BINARY`/`VARBINARY`/`BLOB`, `bytea`, `BIT` | to model with the charsets (1.3 follow-up): byte strings, `binary` collation | changes comparisons |
| PostgreSQL ranges and multiranges | proposed out of scope | PostgreSQL only, no counterpart in the other engines |
| `uuid`, `inet`/`cidr`, `macaddr` | proposed out of scope | PostgreSQL only; text-like semantics |
| Geometric and spatial types (OGC functions) | proposed out of scope | a separate standard (SQL/MM); large |
| Full-text search (`MATCH ... AGAINST`, `tsvector`) | proposed out of scope | relevance ranking is implementation defined |
| XML | proposed out of scope | rarely used in the target engines |

Original plan:
- **Arrays** (PostgreSQL: any type, 1-based, `ARRAY[..]`, `unnest`, `array_agg`, `ANY(array)`, slicing), composite/row types, **ranges and multiranges**, `enum`, `uuid`, `inet/cidr`, `bit`, `bytea`, MySQL `ENUM`/`SET`/`BIT`/`BINARY`/`BLOB`,
  geometric and spatial types (OGC functions: decide scope), full-text (`MATCH .. AGAINST`, `tsvector`/`tsquery`): decide per type whether a full model or an explicit exclusion note in `docs/DIALECTS.md` (with the reason) is right;
  exclusions must be listed in the checklist as "out of scope", not left implicit.
- **Depends on**: 1.2, 1.3.

### 1.8 SQLite dynamic typing — DONE for comparisons (core hook `cmp_coerce` with the affinity of the column
expressions (`attr_affinity`): NUMERIC affinity applied to a TEXT or untyped operand, TEXT affinity to an untyped one;
REAL results and integer overflow with 1.2; `typeof`). Open: affinity of `CAST` expressions and of subquery columns in
`IN`, `BLOB`.
- **What**: five storage classes, column affinity (`INTEGER`, `TEXT`, `BLOB`, `REAL`, `NUMERIC`) applied on comparison and on `CAST`, `typeof`, `||` and arithmetic on all classes, integer overflow to real, `GROUP BY` and
  `DISTINCT` identity of `1` and `1.0`, expression affinity (a column's affinity propagates through `+`? no: only through the column reference and `CAST`).
- **Sources**: `https://www.sqlite.org/datatype3.html`, `src/expr.c` (`sqlite3ExprAffinity`, `sqlite3CompareAffinity`), `src/vdbe.c`.
- **Done when**: the type-affinity tables of the SQLite documentation reproduce, and the `evidence` sqllogictest files for SQLite pass for all queries (today 128).

### 1.9 Implicit conversion matrix and `CAST` — PARTLY DONE

Done (value level): casts per dialect to integer of each width, unsigned, numeric/decimal(p,s), float4/float8/double,
string, boolean, date/time/timestamp/interval, JSON; the conversions of comparisons (MySQL strings to numbers, dates
from strings and numbers, SQLite affinity, PostgreSQL literals read as booleans/dates, Oracle `ORA-01722`). Still to
do, with the static typing of TODO 6.2 on which it depends: the result type of `UNION`, `CASE`, `COALESCE`,
`GREATEST` (PostgreSQL `UNION types ... cannot be matched`, MySQL aggregation of types), and the typing of `NULL` and
of unknown-type literals of PostgreSQL.

Original plan:
- **What**: for each ordered pair of types and each dialect: implicit conversion allowed? result type? error or warning? (e.g. MySQL string to number prefix parse; PostgreSQL no implicit text-to-number but `unknown` literals resolved from context;
  Oracle mode string/number conversion with `NLS` settings; SQLite affinity). `CAST` to each type: parsing rules and failure behaviour. Type resolution for `UNION`, `CASE`, `COALESCE`, `GREATEST`.
- **How**: a type lattice per dialect `common_type : type -> type -> option type`; literal typing; resolved types used by `SELECT`, `UNION`, `VALUES`. Introduce `typeof_sexpr` (static type inference) since conversions depend on static types (ties to 6.2).
- **Sources**: PostgreSQL `src/backend/parser/parse_coerce.c`, `parse_oper.c`; MySQL `sql/item_cmpfunc.cc` (`Arg_comparator`), `sql/field.cc`; TiDB `pkg/expression/builtin_cast.go`, `pkg/types/etc.go`.
- **Depends on**: 1.2–1.8.

### 1.10 `sql_mode` and session variables as parameters — DONE for the MySQL family

Done: `my_session` (`MySQL.v`) with the default collation (padding, case), `div_precision_increment`,
`PIPES_AS_CONCAT`, `ONLY_FULL_GROUP_BY`, `group_concat_max_len`; default sessions of MySQL, MariaDB,
TiDB, OceanBase MySQL mode, Percona, PolarDB from their sources (`Test_Session.v`). The variables which
only change parsing (`ANSI_QUOTES`, `NO_BACKSLASH_ESCAPES`, `HIGH_NOT_PRECEDENCE`) have no counterpart in
the abstract syntax. Still to come with the items they concern: `time_zone`, `DateStyle` (1.5),
`extra_float_digits` (1.2.2), `REAL_AS_FLOAT` (1.2.2), `NO_UNSIGNED_SUBTRACTION` (1.2.3), MariaDB
`sql_mode=ORACLE` (4.3), `tidb_*` and `ob_*` variables that change results (4.4, 4.8).

- **What**: a record `session` with the variables that change query results: `sql_mode` flags (`ANSI_QUOTES`, `PIPES_AS_CONCAT`, `ONLY_FULL_GROUP_BY`, `STRICT_TRANS_TABLES`, `NO_BACKSLASH_ESCAPES`, `PAD_CHAR_TO_FULL_LENGTH`,
  `REAL_AS_FLOAT`, `ERROR_FOR_DIVISION_BY_ZERO`, `ORACLE` in MariaDB, `NO_UNSIGNED_SUBTRACTION`), `div_precision_increment`, `group_concat_max_len`, `time_zone`, `default_collation`, `sql_auto_is_null`,
  PostgreSQL `standard_conforming_strings`, `DateStyle`, `extra_float_digits`, `search_path`, TiDB `tidb_*` that change results, OceanBase `ob_*`.
- **How**: make `vsem` a function of `session` (`vs_of d : session -> vsem`) with the dialect's defaults as `default_session d`; move hard-coded constants (`div_precision_increment`, `pad`, `ci`) into it.
- **Done when**: changing `sql_mode` in a test changes `||`, group-by acceptance, strings escapes as the engine does.

---------------------------------------------------------------------------------------------------------

## Phase 2. Functions, predicates, aggregates: the full lists per dialect

For each family below: (a) extract the engine's own list from its source (MySQL `sql/item_create.cc`; MariaDB `sql/item_create.cc`; PostgreSQL `src/include/catalog/pg_proc.dat` + `pg_operator.dat`; SQLite `src/func.c`, `date.c`, `json.c`,
`window.c` and the documentation of built-in functions; TiDB `pkg/expression/builtin.go` (the `funcs` map) and `pkg/parser/ast/functions.go`; OceanBase `src/sql/engine/expr/*` and `src/objit` function table; Percona/PolarDB: documentation diff against MySQL);
(b) generate a table `docs/functions/<dialect>.md` listing every function, its arity, its families and its status in the model (modelled / excluded with reason / not yet);
(c) model the functions with a source citation, with NULL, empty, error and type-conversion behaviour for each; (d) add acceptance (name, arity, argument types) per dialect; (e) one test file per family with cases from the engine's own test suite or manual.
Targets: every function of the table is either modelled or has an explicit exclusion reason.

- **2.1 Arithmetic and mathematics**: `mod`/`%`/`div`, `sqrt`, `cbrt`, `exp`, `ln`, `log`/`log2`/`log10`, trigonometry, `pi`, `degrees`/`radians`, `ceiling`, `sign`, `width_bucket`, `gcd`/`lcm`, `factorial`, `rand`/`random` (as a nondeterministic function: the set of results),
  bit operators `& | ^ ~ << >>` (MySQL 64-bit unsigned semantics), `bit_count`. Needs 1.2.
  **Status: DONE** — table and sources in `docs/functions/math.md`, tests in `src/testing/Test_Math.v`. The
  transcendental functions are computed exactly in fixed point and rounded once (`IEEE.v`), the `numeric`
  versions of PostgreSQL have the scales of `numeric.c`, the C compositions of each engine are kept
  (MySQL `LOG2`, `COT`, `DEGREES`). Exclusions: `rand()`/`random()` without seed (nondeterministic), `setseed`;
  `RAND(N)` gives the first number of its sequence on every row; OceanBase Oracle mode `NUMBER` math in Phase 4.
- **2.2 Strings**: `lower`, `lpad`/`rpad`, `substring_index`, `translate`, `initcap`, `ascii`/`chr`/`ord`/`char`, `split_part`, `format`, `overlay`, `position`/`strpos`/`locate`/`instr`, `repeat`, `reverse`, `trim` variants (`LEADING`/`TRAILING`/`BOTH`, character sets),
  `concat_ws`, `quote_ident`/`quote_literal`, `md5`/`sha1`/`sha2`, `hex`/`unhex`/`to_base64`, `soundex`, `space`, `insert`, `elt`/`field`/`find_in_set`, `like ... escape`, `ilike`, `similar to`, `regexp_*`. Needs 1.3.
  **Status: DONE** (except `similar to` and `regexp_*`, which are TODO 2.4). The table and the sources are in
  `docs/functions/strings.md`, and the tests in `src/testing/Test_String.v`. Algorithms on code points are in
  `StringFuns.v`, and the digests are in `Hash.v` (MD5, SHA-1, SHA-2, checked on the FIPS/RFC vectors).
  The translator reads `TRIM(... FROM ...)`, `POSITION(a IN b)`, `SUBSTRING(s FROM n FOR m)`,
  `OVERLAY(... PLACING ...)`, `LIKE ... ESCAPE` and `ILIKE`. Exclusions:
  - Unicode case folding: only ASCII is folded (open issue I9, row 24).
  - SQLite `printf`/`format`.
  - PostgreSQL `sha*` of `bytea`.
- **2.3 Comparison and conditional**: `in (list)` and `not in` NULL cases per dialect, `between symmetric`, `<=>`, `is distinct from`, `greatest`/`least` type rules, `decode` (Oracle), `nvl2`, `if`/`iif`/`ifnull`, `coalesce` type resolution, `nullif`.
  **Status: DONE**: the table is in `docs/functions/conditional.md`, the tests in `src/testing/Test_Cond.v`.
  Added in this item:
  - `BETWEEN SYMMETRIC`
  - Oracle `DECODE`
  - SQLite scalar `max`/`min` (the translator tells them from the aggregates by their arity)
  - MySQL `ISNULL()` and `INTERVAL()`
  - PostgreSQL `num_nulls`/`num_nonnulls`
  - SQLite `likely`/`unlikely`

  The result type of `COALESCE`/`CASE`/`GREATEST` is left to static typing (1.9 / 6.2): the value is
  printed the same either way.
- **2.4 Regular expressions**: three engines: PostgreSQL ARE (`~`, `~*`, `regexp_match`, `regexp_replace`, `regexp_split_to_table`), MySQL/MariaDB (ICU in MySQL 8, PCRE in MariaDB 10.0.5+, `REGEXP`, `REGEXP_LIKE/INSTR/REPLACE/SUBSTR`, flags `c i m n u`),
  TiDB (Go RE2 syntax), OceanBase (MySQL mode ICU; Oracle mode POSIX with Oracle flags), SQLite (extension, not built in: `REGEXP` operator calls a user function: record as "absent"). Model: a regex AST, parse per syntax, a matching semantics
  (leftmost-first for Perl-style, leftmost-longest for POSIX), flags, `NULL` handling. Verify the matcher with the engines' regex test files. Needs 1.3.
  **Status: DONE**. The model and its limits are described in `docs/functions/regex.md`.
  - `Regex.v` holds the syntax, the parser per flavour, the backtracking matcher, and the two match
    policies: leftmost-first, and PostgreSQL's greediness-based longest/shortest.
  - `RegexFuns.v` defines the functions of each dialect.
  - `Test_Regex.v` takes its cases from PostgreSQL's `regex.out` and from the manuals.
  - The translator reads `REGEXP`/`RLIKE`, `~`/`~*`/`!~`, `SIMILAR TO` and `substring(... from 'pattern')`.

  Excluded:
  - array-returning functions (`regexp_match`, `regexp_matches`, `regexp_split_*`);
  - the `x` flag and `\p{}` classes;
  - Unicode case folding.
- **2.5 Aggregates**: the list per dialect (`any_value`, `bit_xor`, `std`/`stddev*`, `variance`, `array_agg`, `json_agg`/`json_arrayagg`/`json_objectagg`, `count(distinct a, b)`, `corr`/`covar_*`/`regr_*`, `approx_count_distinct`, `bool_*`, `every`, `string_agg`/`group_concat`/`listagg` with every option,
  `first`/`last` (Oracle `KEEP`), `median`), empty-group results, `DISTINCT` + `FILTER` + `ORDER BY` combinations, overflow of `sum`, type of `sum`/`avg` results per dialect (MySQL `sum` of int is decimal; PostgreSQL `sum(int)` is `bigint`, `sum(bigint)` is `numeric`; SQLite integer overflow error).
  **Status: DONE** — table in `docs/functions/aggregates.md`, tests in `src/testing/Test_Aggregates.v`
  (`Aggregates.v`). Done in this item:
  - variance and standard deviation with each dialect's result type (PostgreSQL `numeric` scales of
    `numeric_stddev_internal`, MySQL `DOUBLE`);
  - the two-variable statistics (`covar_*`, `corr`, `regr_*`);
  - `bit_xor`, and the MySQL unsigned results of `BIT_AND`/`BIT_OR` on the empty group;
  - `any_value`;
  - the JSON aggregates of MySQL and PostgreSQL;
  - `count(distinct a, b)`.

  The translator reads aggregates of two arguments. Excluded:
  - `array_agg` (arrays, 2.8);
  - `approx_count_distinct` (not specified exactly);
  - Oracle `KEEP` (syntax, Phase 3);
  - ordered-set aggregates (2.6).
- **2.6 Ordered-set and hypothetical-set aggregates**: `percentile_cont`, `percentile_disc`, `mode`, `rank/dense_rank/percent_rank/cume_dist(args) WITHIN GROUP`, `MEDIAN` (Oracle, MariaDB window); new syntax `E_AggWithin` carrying the direct arguments and the `WITHIN GROUP (ORDER BY ..)`.
  **Status: DONE**. Documentation is in `docs/functions/aggregates.md` (second part) and tests in
  `src/testing/Test_OrderedSet.v`. No new core node was needed: `E_AggX` carries the direct argument in its
  second slot and the `WITHIN GROUP` ordering as its `ORDER BY`. The translator reads
  `WITHIN GROUP (ORDER BY e [ASC|DESC])`.

  Not modelled:
  - several sort keys or several direct arguments;
  - arrays of fractions;
  - MariaDB's window `MEDIAN` (windows: Phase 3).
- **2.7 Date and time functions**: per family (see 1.5): `extract`, `date_trunc`, `date_add/sub`, `adddate`, `datediff`, `timestampdiff`, `date_format`, `to_char`/`to_date`/`to_timestamp`, `str_to_date`, `strftime`, `julianday`, `now`/`current_*`, `age`, `make_date`, `interval` arithmetic, `last_day`, `add_months`, `months_between`.
  **Status: DONE**. The table is in `docs/functions/datetime.md`, the code in `TemporalFuns.v`, and the tests in `src/testing/Test_DateTime.v`. The functions added by this item:
  - MySQL: `STR_TO_DATE`, `MAKEDATE`/`MAKETIME`, `SEC_TO_TIME`/`TIME_TO_SEC`, `FROM_DAYS`, `FROM_UNIXTIME`, `DAYNAME`/`MONTHNAME`, `PERIOD_*`, `TIMEDIFF`/`ADDTIME`/`SUBTIME`, `TIME_FORMAT`, `UTC_*`, and `EXTRACT` with composite units.
  - PostgreSQL: `age`, `to_date`/`to_timestamp`, `make_time`/`make_timestamp`/`make_interval`, `justify_*`, `date_bin`, `isfinite`, and `clock_timestamp` and its kin.
  - Oracle: `NEXT_DAY`, and `TRUNC`/`ROUND` of dates.

  The translator reads `EXTRACT(unit FROM e)`.

  Not modelled:
  - Zero dates.
  - `justify_interval` sign normalization.
  - `timeofday()`, which is nondeterministic.
- **2.8 JSON and array functions**: see 1.6/1.7: `json_extract`, `json_set`, `json_array`, `json_object`, `json_contains`, `json_length`, `jsonb_*`, `array_*`, `unnest`, `ANY(array)`.
  **Status: DONE** (except the table functions `unnest`, `json_each` and the SQL/JSON path language). The
  table is in `docs/functions/json_arrays.md`, and the tests in `src/testing/Test_JsonFuns.v`.
  - The JSON update functions of each dialect are in `JsonFuns.v`.
  - PostgreSQL arrays are a `Value_J` of kind 2. They print with `array_out`'s rules and compare element by
    element. The array functions, `ANY`/`ALL` over arrays, `@>`, `<@` and `&&` are modelled.
  - The translator reads `ARRAY[...]`, `a[i]`, `a[i:j]` and `op ANY (array)`.
- **2.9 System and information functions**: `version`, `current_user`, `database`, `current_schema`, `connection_id`, `found_rows`, `last_insert_id`, `row_count`: environment-supplied constants.
  **Status: DONE**. The functions read the record `sys_env` of `SystemFuns.v`, whose value `default_env` describes a
  fresh `root` session on database `test`. The table is in `docs/functions/system.md` and the tests in
  `src/testing/Test_System.v`. The translator reads the niladic forms without parentheses (`current_user` …).
  Excluded: nondeterministic or side-effecting functions (`uuid`, `sleep`, `benchmark`) and the catalog functions.
- **2.10 Arity and type checking**: acceptance checks argument counts and (after 1.9) argument types per dialect, with the engine's error; unknown functions are errors, not NULL (today `vs_symb` gives NULL for unknown names).
  **Status: DONE for arity and unknown functions; argument types are part of the static typing of 1.9 / 6.2.**
  - `U_Symbol` carries the number of arguments of a call. `known_symbol` of a dialect checks it against
    the dialect's ranges in `Arity.v`, which are taken from the manuals. Some families differ: MySQL
    `LPAD` takes 3 arguments, MariaDB 2 or 3; SQLite `coalesce` needs 2 arguments; MySQL `GREATEST` needs 2.
  - A call of the wrong arity is rejected by `accepted_by`, and its evaluation is an error.
  - An unknown function is an error at evaluation (`vs_interp_symbol`), not NULL.
  - Tests are in `src/testing/Test_Arity.v`.
- **2.11 Provenance table**: every entry of every table has a `source` field (file/page) kept in a generated markdown (`docs/functions/*.md`); a script checks that no entry lacks one.
  **Status: DONE**. Every entry of the function, predicate and aggregate tables is documented, with its sources, in one of the
  tables of `docs/functions/` (`math`, `strings`, `conditional`, `regex`, `aggregates`, `datetime`,
  `json_arrays`, `system`, and `core` for the operators, casts, Phase 1 functions and internal names).
  - `tools/functions/check_provenance.py` extracts the names from the Coq sources and checks that each one
    is documented.
  - With `--write`, it regenerates `docs/functions/INDEX.md`: every name, the files which define it and the
    document which describes it. The table has 421 names and none is missing.
  - The check runs in CI (`.github/workflows/build.yml`).
  - The source is a row of a document, not a field of the Coq tables: the tables stay plain lists of
    functions.

---------------------------------------------------------------------------------------------------------

## Phase 3. Remaining constructs of the query language (`SqlFull.v`)

- **3.1 Window functions, completion**: frame exclusion `EXCLUDE CURRENT ROW | GROUP | TIES | NO OTHERS`; `RANGE` with decimal, float, date and `INTERVAL` offsets (needs 1.2, 1.5); `IGNORE NULLS`/`RESPECT NULLS` and `FROM FIRST/LAST` for `nth_value`/`lag`/`lead`/`first_value`;
  named windows (`WINDOW w AS (..)`, inheritance `OVER (w ORDER BY ..)`); window functions inside `ORDER BY` and in expressions with `DISTINCT`; the default frame rule when `ORDER BY` is present or absent; `lag`/`lead` with negative or zero offsets and defaults of other types; `ntile` with NULL.
  *Done when* the PostgreSQL `window.sql` regression file and MySQL `window_functions*.test` translate and pass.
  **Status: DONE in the core**. Tests are in `src/testing/Test_Window2.v`. Added:
  - frame exclusion: `Frame_Excl` with `EXCLUDE CURRENT ROW | GROUP | TIES | NO OTHERS`;
  - rational `RANGE` offsets (`Preceding_Q`/`Following_Q`): decimals and doubles, and intervals over
    `DATE` keys (in days) or `TIMESTAMP` keys (in microseconds), as `rat_of_value` maps temporal keys to
    those units;
  - `IGNORE NULLS` and `FROM LAST` (`W_Opts`) for `first_value`, `last_value`, `nth_value`, `lag`, `lead`;
  - the features `F_Frame_Exclusion` (PostgreSQL, SQLite), and `F_Null_Treatment` and `F_From_Last`
    (Oracle mode only), checked by acceptance.

  Other notes:
  - Named windows (`WINDOW w AS (...)`, `OVER (w ORDER BY ...)`) are a derived form: the translator
    expands them.
  - The default frame was already modelled (`default_frame`).
  - Offsets of `lag`/`lead` are natural numbers: a negative offset is an error in the engines.
  - Not modelled: `RANGE` offsets in months, `INTERVAL` offsets over `TIME` with wrap-around.
  - Replaying PostgreSQL's `window.sql` needs the PostgreSQL regression harness of Phase 5.2.
- **3.2 Joins**: `USING` (merged column, order of columns in `SELECT *`, `NATURAL` over several columns with the engine's column ordering), `JOIN ... ON` with outer joins and `WHERE` pushdown independence (semantic equivalence lemmas), comma joins precedence vs `JOIN` (MySQL: `JOIN` binds tighter than comma),
  `STRAIGHT_JOIN`, semi/anti joins (`LEFT SEMI`, not SQL), `CROSS APPLY`/`OUTER APPLY` (Oracle mode: `LATERAL` forms), `(+)` Oracle outer-join operator, full join `ON` with non-equi conditions.
  **Status: DONE**. Tests are in `src/testing/Test_Joins.v`, and OceanBase's `join_using1` (12 queries) passes.

  The translator handles the join syntax:
  - `USING` and `NATURAL`: the join is on the equality of the common columns, and an unqualified
    reference to a merged column is the left column (the right one for `RIGHT JOIN`, their `COALESCE`
    for `FULL JOIN`).
  - `SELECT *` lists the merged columns first. The other columns follow, the right operand's first for
    `RIGHT JOIN`, as MySQL does.
  - A comma binds less than `JOIN`: `a, b JOIN c ON ...` is `a, (b JOIN c ON ...)`.
  - `STRAIGHT_JOIN` is read.

  The core and the derived forms:
  - Pushing a condition down into an inner join's `ON` is proved: `inner_join_where` in `SqlFullFacts.v`.
  - For an outer join, a test shows that `ON` and `WHERE` differ.
  - New derived forms: `straight_join` (an inner join), and `cross_apply`/`outer_apply` (lateral inner and
    left joins). The Oracle `(+)` operator is written as the corresponding outer join, as documented in
    `SqlFullSyntax.v`.
  - Full joins with a non-equality `ON` condition are covered by the general join, and tested.

  Not modelled: semi- and anti-joins, which are not SQL syntax.
- **3.3 Set operations**: precedence (`INTERSECT` before `UNION`/`EXCEPT`; MySQL 8.0.31+ same), parenthesised operands with their own `ORDER BY`/`LIMIT`, column naming and type unification (`UNION` of int and decimal), `MINUS` (Oracle), `EXCEPT ALL`/`INTERSECT ALL` multiplicity laws, `CORRESPONDING` (not in these engines: exclusion note), and NULL-equality in set operations per collation.
  **Status: DONE**. Tests are in `src/testing/Test_SetOps.v`.
  - Precedence (translator): `INTERSECT` binds tighter than `UNION`/`EXCEPT` for PostgreSQL and MySQL. SQLite and Oracle give them the same precedence, from left to right.
  - Parenthesized operands keep their own `ORDER BY`/`LIMIT` (`order_limit` inside `SQ_Set`).
  - Type unification: the new dialect field `unify_column` (`vs_unify`) converts the values of each
    column of a set operation to the column's type. MySQL gives a `DECIMAL` column the largest scale
    (`SELECT 1 UNION SELECT 2.5` gives `1.0`, `2.5`); PostgreSQL and SQLite leave the values.
    `union_all_spec` now states its hypothesis that the dialect leaves the values.
  - The column names of a set operation are those of the first operand (translator).
  - `MINUS` is `EXCEPT` (`Diff`).
  - The multiplicities of `EXCEPT ALL`/`INTERSECT ALL` are tested (`max(m - n, 0)` and `min(m, n)`).
  - NULLs are not distinct from each other in set operations, and equality follows the dialect's collation.
  - `CORRESPONDING` is in none of the engines and is excluded.
- **3.4 Table functions and sources**: `generate_series`, `unnest ... WITH ORDINALITY`, `json_table`/`JSON_TABLE`, `json_each`/`json_tree`, `jsonb_array_elements`, `string_to_table`, `regexp_split_to_table`, `XMLTABLE` (decide scope), `(VALUES ...) AS t(a, b)`, `TABLE t`, `SELECT` without `FROM`, `DUAL`, SQLite virtual tables and `pragma_*` table-valued functions, `INFORMATION_SCHEMA` as ordinary tables with engine-specific contents.
  **Status: DONE**, tested in `src/testing/Test_TableFuns.v`. The scope decisions are below.
  - New core source `Fr_Fun name args ordinality atts`. A new dialect field `table_fun` gives the rows of
    a call, and acceptance rejects an unknown table function (`U_Table_Fun`). In a lateral join, the
    arguments read the rows on the left; a table function after a comma is lateral, as in PostgreSQL.
  - PostgreSQL:
    - `generate_series` over integers, `numeric` and timestamps with an interval step (a zero step is an error);
    - `unnest` of several arrays, with NULL padding;
    - `json(b)_array_elements(_text)`, `json(b)_each(_text)`, `json(b)_object_keys`;
    - `string_to_table`, `regexp_split_to_table`;
    - `WITH ORDINALITY`.
  - MySQL: `JSON_TABLE` with `PATH` columns. The column types, `FOR ORDINALITY` and `ON EMPTY/ERROR` are
    not modelled.
  - SQLite: `json_each`, with its eight visible columns. `id` numbers the rows; SQLite gives a node offset.
  - Sources that already existed: `(VALUES ...) AS t(a, b)` (`values_` + `from_as`) and `SELECT` without
    `FROM`.
  - Translator: reads `FROM DUAL`, table functions in `FROM` (PostgreSQL, SQLite) and MySQL `JSON_TABLE`.
  - `TABLE t` is `SELECT * FROM t` (a derived form).
  - Excluded:
    - `json_tree` and `XMLTABLE` (XML is not modelled);
    - SQLite `pragma_*` and other virtual tables, and `INFORMATION_SCHEMA`: they read the catalog,
      which the model does not have;
    - `generate_series` in SQLite (an extension, not in the core library).
- **3.5 `GROUP BY` / `ORDER BY` forms**: ordinals (`GROUP BY 1`), output aliases (MySQL/SQLite allow in `GROUP BY`/`HAVING`/`ORDER BY`; PostgreSQL only in `ORDER BY` and `GROUP BY`), expressions over aliases; `GROUP BY ... WITH ROLLUP` ordering details (MySQL `GROUPING()`, sort of result); `ORDER BY` with `COLLATE`; the ordering of NULLs per type; `ORDER BY` inside views and subqueries (ignored unless `LIMIT`); stable vs unspecified sort of ties (set-valued result: `results : set of lists`).
  **Status: DONE**. Ordinals and aliases are name resolution, which the translator does before the
  core sees a query. The core works on the resolved expressions.
  - `GROUP BY`/`ORDER BY` ordinals: done.
  - Aliases:
    - in `GROUP BY`, the tables come first and then the aliases (MySQL, SQLite);
    - a bare alias in `ORDER BY` comes first;
    - aliases inside `ORDER BY` expressions (MySQL, SQLite);
    - aliases in `HAVING`: MySQL looks at the aliases first, SQLite only for names that are not columns,
      and PostgreSQL rejects them (an unknown column).
  - `WITH ROLLUP` is `G_Rollup`. Its rows are a bag; the engines do not specify their order without
    `ORDER BY`.
  - `ORDER BY ... COLLATE` is an ordering key with `collate`.
  - NULLs in ordering: `nulls_smallest` per dialect and `NULLS FIRST/LAST` (1.4).
  - An `ORDER BY` inside a subquery is kept as a list, which the enclosing block reads as a bag; it
    matters with `LIMIT`/`FETCH`.
  - The order of ties is not specified. The conformance runner accepts any order of rows with equal
    keys only for the unordered comparison; making results a set of possible lists is item 3.10.
- **3.6 Recursion**: multiple CTEs referencing each other, mutual recursion (`WITH RECURSIVE a ..., b ...`), `SEARCH DEPTH/BREADTH FIRST`, `CYCLE` (PostgreSQL, Oracle), recursive CTE restrictions per engine (no aggregates in the recursive term in MySQL, `UNION` vs `UNION ALL`, `LIMIT` in recursive term, data type of the anchor decides column types and truncation in MySQL), per-engine recursion limits (`cte_max_recursion_depth` = 1000 in MySQL/MariaDB/TiDB errors instead of returning the first 1000 steps, which today's `rec_fuel` does: change to an error after 1.1).
  **Status: DONE** (tests in `src/testing/Test_Recursive.v` and `Test_Recursive2.v`).
  - Recursion limit: a recursion with no fixpoint within `rec_fuel` = 1000 steps is a failed row. MySQL,
    MariaDB and TiDB fail there (`cte_max_recursion_depth`). PostgreSQL and SQLite do not terminate,
    which is a failure of the evaluation too.
  - CTEs that refer to the CTEs before them are nested `SQ_With`.
  - Mutual recursion is in none of the engines (PostgreSQL: "mutual recursion between WITH items is not
    implemented") and is excluded.
  - `SEARCH`/`CYCLE` are written as PostgreSQL's manual defines them (7.8.2.2): a depth column, or a path
    array with `= ANY(path)`. The arrays of 2.8 make the `CYCLE` rewriting run; it is tested on a cyclic
    graph.
  - An aggregate or a `GROUP BY` in the recursive term is rejected by acceptance in every dialect: new
    feature `F_Rec_Aggregate`, computed by `rec_term_groups`.
  - `UNION` and `UNION ALL` are both modelled.
  - Not modelled: the MySQL rule that the anchor's types decide the column types (and truncation
    errors), which needs static typing (1.9 / 6.2); `LIMIT` in the recursive term.
- **3.7 Row values**: `(a, b) < (c, d)`, `(a, b) = (SELECT ..)`, `ROW(..)`, row `IN` with NULLs, `OVERLAPS`, `(a,b) IS NULL`; per-dialect restrictions.
  **Status: DONE**, tested in `src/testing/Test_Rows.v`.
  - Row comparisons `row< row<= row> row>=`: the first pair that is not equal decides, and a NULL before
    the decision makes the result UNKNOWN. They join the existing `row=`/`row<>`.
  - `(a, b) IS [NOT] NULL` (`row is null`, `row is not null`) for every dialect.
  - PostgreSQL `OVERLAPS`: an end may be an interval from its start, and the ends are swapped when
    reversed. The manual's examples are tested.
  - Row `IN` with NULLs is `C_In`, already modelled.
  - `ROW(...)` and the parenthesized row are the same syntax (translator).
  - `(a, b) = (SELECT ...)` with a one-row subquery is written `(a, b) IN (SELECT ...)`. With several
    rows, the engines raise an error; the model gives the `IN` result instead (a documented difference).
- **3.8 Scalar subquery and `EXISTS` details**: more than one row is an error (needs 1.1) except in `LIMIT 1` forms; zero rows gives NULL; `ANY`/`ALL` with empty sets; `IN` with `UNION` subqueries; correlated references in `ORDER BY`/`GROUP BY`/`HAVING`; `LATERAL` references to window-function outputs.
  **Status: DONE**, tested in `src/testing/Test_Subqueries.v`.
  - A scalar subquery with two rows is an error in PostgreSQL and MySQL, and the first row in SQLite
    (`scalar_first_row`). With no row, it is NULL.
  - `ALL` of an empty set is true and `ANY` of it is false; with a NULL, `ALL` and `ANY` are three-valued.
  - `IN` over a `UNION` and `NOT EXISTS` are tested.
  - A correlated subquery in `HAVING` reads the group's column.
  - A `LATERAL` reference to a window output is a lateral join over `SQ_Window`, which needs nothing new.
- **3.9 Output naming and column identity**: the names of output columns for unnamed expressions (`?column?`, `count(*)`), duplicate names in derived tables (error in PostgreSQL/MySQL `Duplicate column name` when referenced, allowed in outputs), positional semantics (I4), `SELECT *` over joins and `USING`, qualified names `t.*`, ambiguous column errors.
  **Status: DONE** (`src/data/proof_of_concept/Naming.v`, `src/testing/Test_Naming.v`).
  - `pg_colname` is PostgreSQL's `FigureColname`: a column gives its name, a function or an aggregate
    its name (`count(*)` gives `count`), a cast the type name, `CASE` gives `case`, and anything else
    `?column?`.
  - MySQL and SQLite name such a column by the text of the expression; the translator keeps the text.
  - Name resolution (the translator) handles the rest:
    - duplicate names are allowed in a result, and a derived table with duplicate names is not
      translated (the engines raise an error when it is referred to by name);
    - `SELECT *` over joins and `USING` (3.2);
    - an ambiguous or unknown column is the engine's error, and the query is not translated;
    - `t.*` is still skipped by the translator.
  - The positional semantics (I4) is unchanged: the outputs are the attributes `c0, c1, ...`.
- **3.10 Non-determinism and environment**: model the choice of rows as a set of allowed results: `LIMIT` without `ORDER BY`, ties, bare columns, `RANDOM`, `NOW`, `UUID()`; a semantic function `eval_query_set : ... -> list tuple -> Prop` (is this multiset a possible result) alongside the executable one; use it in the conformance harness instead of skipping those queries.
  **Status: DONE for ties and `LIMIT` without `ORDER BY`.**
  - In the core (`SqlFull.v`):
    - `order_groups` gives the groups of peers of an ordered query, with its `LIMIT`.
    - `allowed_ordered` is a `Prop`: a result is allowed if it orders the rows of each group in any way
      (`Forall2 Permutation`) and, at the `LIMIT`, keeps any of the boundary peers.
    - `allowed_ordered_refl` proves that the evaluation's own order is allowed.
  - In the runner (`SpecRunner.v`):
    - `ties_ok` is the executable test of `allowed_ordered`;
    - `mk_case_limit` checks that a `LIMIT n` without `ORDER BY` gives any `n` rows of the result
      (`sub_bag`).
    - The two former OceanBase tie failures (`expr_floor:56/57`) now pass, and the queries with a
      `LIMIT` but no `ORDER BY` are translated.
  - The other sources of nondeterminism:
    - `NOW` is the fixed statement time.
    - `RANDOM`/`UUID` are excluded (2.1, 2.9).
    - The value of a bare column (any row of its group) is not modelled: those queries are still not
      translated.
- **3.11 Statements accepted and ignored**: `FOR UPDATE`, `FOR SHARE`, `LOCK IN SHARE MODE`, `SKIP LOCKED`, optimizer hints, `SELECT ... INTO`, `EXPLAIN` (no result semantics): parsed and accepted with no effect, recorded per dialect.
  **Status: DONE** (translator).
  - `FOR UPDATE [OF t] [NOWAIT | SKIP LOCKED | WAIT n]`, `FOR SHARE` and `LOCK IN SHARE MODE` are read
    and have no effect on the rows of the query.
  - Optimizer hints (`/*+ ... */`) are comments.
  - `SELECT ... INTO` (variables, files) and `EXPLAIN` return no rows of the query: they are not
    queries of the model, and the translator skips them.

---------------------------------------------------------------------------------------------------------

## Phase 4. Dialect closeouts

For each dialect, a closeout is: the engine's SQL reference read end to end for the `SELECT` statement and its expression language, every construct and function either modelled or excluded with a reason, a `docs/DIALECTS.md` section, and the validation of Phase 5.

- **4.1 PostgreSQL** (target 17; also 12–16 flags): types (1.2–1.7), full operator and function catalogue (`pg_proc.dat`, `pg_operator.dat`), `search_path`/`pg_catalog`, `INSERT ... RETURNING`-free; `TABLESAMPLE` (random: set-valued), `FETCH`, `GROUPING SETS`, `LATERAL`, `jsonb`, arrays, ranges, `DISTINCT ON`, `WITH ... MATERIALIZED`, `SEARCH/CYCLE`, `ORDER BY ... USING op`, collations, `interval` styles, `ROWS FROM`, `GENERATED`-column-free.
  **Status: DONE** (`docs/closeouts/PostgreSQL.md`, generated by `tools/functions/closeout.sh`; constructs in `docs/DIALECTS.md` "Closeouts"; added `scale`, `min_scale`, `trim_scale`, `to_bin`, `to_oct`, `array_reverse`, `trim_array` and the internal synonyms).
- **4.2 MySQL** (8.0, 8.4, and 5.7 flags): `sql_mode` matrix, `HAVING` on aliases, `GROUP BY ... WITH ROLLUP`, JSON, `MATCH AGAINST`, `REGEXP` (ICU), full function list, `utf8mb4_0900_*` collations, `LIMIT` forms (`LIMIT offset, count`), `TABLE`/`VALUES` statements, `INTERSECT`/`EXCEPT` (8.0.31+), `LATERAL` (8.0.14+), `WITH ROLLUP`, user variables `@a := ..` (order of evaluation: unspecified), `SELECT ... INTO`, hints, `DIV`/`MOD`, bit semantics.
  **Status: DONE** (`docs/closeouts/MySQL.md`; constructs in `docs/DIALECTS.md`; added `conv`, `bin`, `oct`, `crc32`, `inet_aton`, `inet_ntoa`, `is_ipv4`, `quote`, `any_value`, `make_set`, `export_set`, `weekofyear` and synonyms).
- **4.3 MariaDB** (10.6 LTS, 10.11 LTS, 11.4 LTS, 12.x): its own function list and differences (`sql/item_create.cc`: `NATURAL_SORT_KEY`, `JSON_*`, `REGEXP_*` PCRE, `INTERSECT/EXCEPT` since 10.3, `FETCH FIRST ... WITH TIES` since 10.6, `ROWNUM()`, `SEQUENCE`s `NEXTVAL`), Oracle mode (`sql_mode=ORACLE`: `||`, `NVL`, `DECODE`, `ROWNUM`, `MINUS`, sequences, `DUAL`), `uca1400` collations, system-versioned tables (`FOR SYSTEM_TIME`: decide scope), `WITH ROLLUP`, windows `MEDIAN`, `PERCENTILE_*`, `OFFSET ... FETCH`.
  **Status: DONE** (`docs/closeouts/MariaDB.md`; `docs/DIALECTS.md`).
- **4.4 TiDB** (7.5 LTS, 8.5 LTS, master): the `funcs` map of `pkg/expression/builtin.go` function by function, new collation framework (`utf8mb4_bin`, `utf8mb4_general_ci`, `utf8mb4_unicode_ci`, `utf8mb4_0900_ai_ci`, `gbk_*`), `tidb_*` variables that change semantics (`tidb_enable_*`, `tidb_opt_*` do not; `tidb_sql_mode`), `LIMIT` semantics, `SELECT ... AS OF TIMESTAMP` (stale read: decide scope), `TABLESAMPLE`, `LATERAL`, `FULL OUTER JOIN`, `INTERSECT/EXCEPT [ALL]`, recursive CTEs, windows, `ROLLUP` + `GROUPING`, `JSON`, `REGEXP` (RE2), integer overflow rules, differences from MySQL listed in `docs/pingcap` "MySQL Compatibility".
  **Status: DONE** (`docs/closeouts/TiDB.md`; `docs/DIALECTS.md`).
- **4.5 Percona Server** (8.0, 8.4): diff against MySQL from Percona's source (`percona/percona-server`: clone it, diff `sql/` against `mysql/mysql-server` at the base version): extra functions (`HASH`/`DIGEST`-style, `COMPRESS` variants), system variables that affect queries, extended `SHOW`; record "no differences" where true, with the commit evidence.
  **Status: DONE** (`docs/DIALECTS.md`: same SQL layer as MySQL; the diff from source is open (source not available)).
- **4.6 PolarDB** (MySQL edition 5.6/5.7/8.0, 8.0.1/8.0.2): from the Alibaba documentation: per-minor-version compatibility with MySQL (the table in "Engine versions"), PolarDB-specific hints and parallel query (no result effect), `IMCI` columnar engine differences (decide scope), `FOR UPDATE` handling, and a separate decision record for PolarDB-X (distributed MySQL-compatible) and the PostgreSQL/Oracle-compatible editions: add as dialects or exclude with reasons.
  **Status: DONE** (`docs/DIALECTS.md`: decision on PolarDB-X and the other editions recorded).
- **4.7 SQLite** (3.45 and the current version): full function list (`func.c`, `date.c`, `json.c`, `math` extension, `window.c`), `string_agg`/`group_concat` ordered form, `ORDER BY ... NULLS`, `RETURNING`-free, `WITHOUT ROWID`-free, `INDEXED BY` (no result effect), generated columns-free, `ROWID` and `_rowid_` pseudo-columns, `typeof`, `LIMIT` expressions, `VALUES` forms, the `bare column` rule for `min`/`max`, `pragma` effects (`case_sensitive_like`, `reverse_unordered_selects`, `legacy_alter_table`: document which change results).
  **Status: DONE** (`docs/closeouts/SQLite.md`; `docs/DIALECTS.md`).
- **4.8 OceanBase MySQL mode** (4.2 LTS, 4.3, 4.4): function list from `src/sql/engine/expr/ob_expr_*.cpp` and the expression registry (`ob_expr_operator_factory.cpp`), type system `ObObjType`, `ob_*` variables, hints with semantic effect (`/*+ NO_REWRITE */` has none), `LIMIT`, recursive CTEs, `GROUPING SETS` in MySQL mode, JSON, partition-pruning free; refine its remaining 6 conformance failures.
  **Status: DONE** (`docs/closeouts/OceanBaseMySQL.md`, `OceanBaseOracle.md`; `docs/DIALECTS.md`; conformance 768/769).
- **4.9 OceanBase Oracle mode**: the Oracle SQL language reference as OceanBase implements it (`docs`: Oracle mode SQL reference, `sql_parser_oracle_mode.y` is in the closed enterprise source: from documentation only: record that and list every behaviour taken from documentation vs from shared source); `ROWNUM`, `ROWID`, `CONNECT BY`/`START WITH`/`PRIOR`/`LEVEL` (hierarchical queries: model), `DECODE`, `NVL*`, `MINUS`, `(+)`, `DUAL`, `TO_CHAR`/`TO_DATE`/`TO_NUMBER` with format models, `||` with NULL as empty, `''` as NULL, `LISTAGG`, `PIVOT`/`UNPIVOT` (model as derived forms), `MODEL` clause (decide scope), `SAMPLE`, `FETCH FIRST`, `LATERAL`/`CROSS APPLY`, analytic functions with `KEEP (DENSE_RANK FIRST)`.
  **Status: DONE.** `docs/DIALECTS.md` "OceanBase Oracle mode" lists every construct with its source (shared engine
  source or documentation) and the exclusions with their reasons (`(+)`, `ROWID`, `SAMPLE`, `MODEL`, `KEEP`, `NOCYCLE`).
  `CONNECT BY`, `ROWNUM <=`, `PIVOT`, `UNPIVOT` are derived forms in `SqlFullSyntax.v` (`connect_by`, `rownum_le`,
  `pivot`, `unpivot`); `TO_NUMBER` added; tests in `src/testing/Test_OracleForms.v`.
- **4.10 Per-version flags**: a `version` parameter on each dialect record, and `supports d v feature`; tests that a construct introduced in version N is rejected before it.
  **Status: DONE** (`src/data/dialects/Versions.v`, `src/testing/Test_Versions.v`; the values of functions do not depend on the version).
- **4.11 Decide the scope of further engines** (Oracle Database, SQL Server, DuckDB, ClickHouse, CockroachDB, Snowflake, BigQuery): a short decision record in `docs/OPEN_ISSUES.md` for the user; do not start them before it is answered.
  **Status: DONE** (decision record D1 in `docs/OPEN_ISSUES.md`, awaiting the answer).

---------------------------------------------------------------------------------------------------------

## Phase 5. Validation against real engines

- **5.1 Translator coverage**: extend `tools/spec/sql2coq.py` / `slt2coq.py` to the whole fragment: window functions, `WITH [RECURSIVE]`, `GROUPING SETS`/`ROLLUP`/`CUBE`, ordered aggregates, `DISTINCT ON`, `FETCH ... WITH TIES`, `VALUES`, derived columns lists, dates, JSON.
  **Status: DONE** for window functions, `WITH [RECURSIVE]`, grouping sets, ordered aggregates, `VALUES`, derived column lists, views, dates, JSON; skips are counted by reason in each run's statistics.
  Each translated construct must reproduce a recorded result, otherwise the case is skipped and counted by reason (a skip report, with the reasons, checked in per run).
- **5.2 MySQL-family suites**: MariaDB `mysql-test/main/*.test` + `.result` (functions, window functions `win*.test`, CTEs, `intersect*.test`, `except*.test`, `fetch_first.test`), MySQL `mysql-test/t` and `r` (BSD/GPL: do not copy the data: replay, as with OceanBase),
  **Status: DONE** (`tools/spec/suite_run.sh`; MariaDB, TiDB and MySQL suites replayed, the failures grouped and explained in `docs/CONFORMANCE.md`; Percona and PolarDB have no open suite of their own: they are MySQL's).
  TiDB `tests/integrationtest/t` and `r`, Percona (same as MySQL plus its own), PolarDB (no open suite: use the MySQL one and the documented exceptions). Goal: a table in `docs/CONFORMANCE.md` of queries replayed and passed per dialect, with the failure list explained.
- **5.3 PostgreSQL regression suite**: `src/test/regress/sql/*.sql` and `expected/*.out` (`select.sql`, `aggregates.sql`, `window.sql`, `with.sql`, `join.sql`, `subselect.sql`, `union.sql`, `numeric.sql`, `strings.sql`, `text.sql`, `float8.sql`, `date.sql`, `timestamp.sql`, `json.sql`, `jsonb.sql`, `arrays.sql`, `groupingsets.sql`): the expected files print result tables; write the parser for that format.
  **Status: DONE** (harness `tools/spec/pg_run.sh`, `pg2result.py`; run 1: 232/320, the failures classified in `docs/CONFORMANCE.md`; window functions are not translated yet: 5.1).
- **5.4 SQLite tests**: `test/*.test` TCL files are hard to replay; use the sqllogictest corpus fully (`test/select*.test`, `index/*`, `evidence/*`) for SQLite, and the `sqlite3` CLI's own results (not available here: see 5.7).
- **5.5 OceanBase**: finish the 6 failures (1.2.1), add the Oracle-mode cases that the documentation gives with outputs (the documentation's examples with printed results are a source of recorded results: extract them).
- **5.6 Bug reports as regression cases**: from the two papers (ValScope OSDI '26, Pinolo ATC '23) and the bug trackers of MySQL, MariaDB, TiDB, OceanBase, Percona, PolarDB: for each logic bug, the query and the correct result as documented by the fix; run against the model; any mismatch is either a model defect or a documented engine bug (kept in `docs/ENGINE_BUGS.md` with the model result).
  **Status: PARTIAL.** `docs/ENGINE_BUGS.md`, `tools/spec/engine_bugs/`: 4 confirmed bugs (TiDB #38756, #40015, MariaDB MDEV-30255, MySQL #119321) whose correct results come from the fixes or the developers; the model gives the correct result for all four. Open: the other confirmed MySQL and MariaDB bugs of the Pinolo and ValScope lists, whose report pages the network of the development environment blocks.
  *The model's results define the expected semantics; where an engine deviates, the deviation is recorded, not copied.*
- **5.7 Live engines**: when an environment with engines is available (Docker or a permitted host), a differential script: generate queries from a grammar of the fragment, run on the engine, compare with the model's `vm_compute`/extracted interpreter; until then, record that no live differential result exists.
- **5.8 Metamorphic checks inside Coq**: prove or test the oracles of the tools: Pinolo's containment relations, ValScope's value-semantics rules, TLP (`p`, `NOT p`, `p IS NULL` partition), NoREC, PQS, as lemmas over the model for each dialect (see 6.4), so that a tool's oracle is justified by the semantics, and counterexamples are found by the model first.
  **Status: PARTIAL.** `src/data/sql/Oracles.v`: TLP (`tlp_partition`: the rows are, as a bag, those where `p`, `NOT p`, `p IS NULL` hold; `tlp_sum` for sums and counts) and NoREC (`norec`), over three-valued logic. Open: Pinolo's containment relations and ValScope's value rules, and the statements over `eval_squery` of each dialect.
- **5.9 CI**: the build workflow checks every conformance sample; add a job that regenerates samples from the checked-in generator and fails on a diff; budget the build time (split into jobs).

---------------------------------------------------------------------------------------------------------

## Phase 6. Metatheory and quality of the formalisation

- **6.1 Relate `SqlFull.v` to `Sql.v`/`SqlAlgebra.v` (I2)**: prove that on the fragment of `Sql.v` (no `ORDER BY`, windows, outer joins, `WITH`) `eval_squery` equals `eval_sql_query` as bags; fix or document `Sql.v` deviations A4 and A6; port the algebra equivalence to the new semantics for the common fragment.
- **6.2 Well-formedness and static typing (I5)**: `wf_query : senv_sorts -> squery -> Prop` and `typeof_query`; scoping of columns, aggregate placement (aggregate in `WHERE` is an error), ambiguity, arity of set operations, `GROUP BY` coverage (`ONLY_FULL_GROUP_BY` with functional dependencies from declared keys), type checking per dialect (1.9); theorem: well-formed queries evaluate without a scoping error and the result has the inferred sort.
  **Status: PARTIAL.** `src/data/sql/SqlWellFormed.v`: `wf_query` checks scoping (no free column: `squery_cols`), no aggregate of a block in its `WHERE`, and equal sorts of the operands of set operations, through the `FROM` and `WITH` clauses; `accepted_wf` is acceptance plus `wf_query`; tests in `src/testing/Test_WellFormed.v`. Open: the type checking per dialect (1.9), `GROUP BY` coverage with functional dependencies, ambiguity, and the theorem relating `wf_query` to evaluation.
  `accepted_by` becomes `wf` plus feature acceptance.
- **6.3 Positional semantics (I4)**: tuples as lists with column names as metadata, so duplicate names and `SELECT *` over joins behave as in SQL; migrate `SqlFull.v` and keep a named view for the old lemmas.
- **6.4 Theorems**: determinism and termination of `eval_squery` (structural plus fuel in recursion: show the fuel bound is irrelevant when a fixpoint exists before `rec_fuel` steps); set-operation laws (`UNION` commutative and associative as bags, `INTERSECT ALL` multiplicity); join laws (inner join commutativity up to column order, left join as inner join union padded rows); `DISTINCT` idempotence;
  **Status: PARTIAL.** Proved: `order_by_nothing`, `inner_join_spec`, `inner_join_where` (pushdown through an inner join), `union_all_spec`, `union_all_comm` (as bags), `union_all_assoc`, `dedup_idem` (`DISTINCT` is idempotent), `rollup_sets_length`, `cube_sets_length` (the grouping sets of `ROLLUP` and `CUBE`), `frame_running` (`ROWS UNBOUNDED PRECEDING .. CURRENT ROW` is the running frame), `frame_whole_partition`, TLP and NoREC (`Oracles.v`), `left_join_no_padding`, three-valued logic laws. Open: determinism and fuel irrelevance, the grouping-set decomposition as a `UNION ALL` of queries, the other frame laws, the refinement theorem between dialects.
  `WHERE` pushdown through inner joins; grouping-set decomposition (`ROLLUP (a,b)` equals the `UNION ALL` of its grouping sets with `NULL`s); window frame laws (`ROWS UNBOUNDED PRECEDING..CURRENT ROW` equals running aggregate); three-valued logic laws of the dialects (`TLP`); `to_dialect` is the identity on semantics when the dialects agree on the value interpretations used (a refinement theorem between dialect instances).
- **6.5 `FreshAttr.v`**: prove `fresh_attr_is_fresh` (injectivity of the decimal printing of naturals and pigeonhole), add it to `_CoqProject`, remove `Admitted`.
  **Status: DONE** (`fresh_attr_is_fresh` proved: injectivity of the decimal printing and the pigeonhole principle; the file is built; the two `Admitted` of `SqlAlgebra.v` that depended on it are proved too).
- **6.6 Executable interpreter**: extraction of `eval_squery` and the dialect tables to OCaml with a driver that reads SQL text (via the frontend 7.1) and CSV tables and prints results; test it against `vm_compute` on the whole conformance corpus; measure performance (the Coq `vm_compute` is quadratic in places: `sort_on`, `group_on`, set operations on lists: replace by balanced structures with proved equivalence if needed).
  **Status: PARTIAL.** `tools/extraction/build.sh DIALECT OUTDIR` extracts the semantics, the dialects, `SpecRunner.diagnose`
  and the compiled conformance cases to OCaml (`ExtrOcamlNativeString`; `fix_weak.py` annotates the partial applications
  OCaml cannot generalise), compiles them with `ocamlopt` and runs them. On the OceanBase corpus (66 files, 769 cases) the
  extracted program reports the same failures as `vm_compute` (none) in 48 s, where the Coq run takes about an hour.
  Open: the driver for SQL text and CSV tables (it needs the frontend of 7.1), and the balanced structures.
- **6.7 Coq hygiene**: no `Admitted`, no `Axiom`; `Print Assumptions` for each theorem in CI; module structure so the core (`SqlFull.v`) does not import any dialect; each dialect file imports only `Dialects.v` and `ValueKit.v`.
  **Status: DONE.** CI checks that no built file has `Admitted`, `admit` or `Axiom`, that the core (`src/data/sql/`) imports no dialect, that a dialect imports no other dialect (the members of the MySQL family import `MySQL.v`, of which they are instances: `mysql_vs`), and that the main results are closed under the global context (`src/testing/Assumptions.v`). The shared helpers (`canon_numeric`, `my_truth`, `case_by`, `z_arg`, ...) are in `ValueKit.v`.

---------------------------------------------------------------------------------------------------------

## Phase 7. Frontend, documentation and process

- **7.1 SQL frontend**: a lexer and parser per dialect family (PostgreSQL, MySQL family, SQLite, OceanBase Oracle) to `SqlFull` syntax, written in OCaml or Python (Python acceptable for tooling; OCaml to link with extraction): replaces `sql2coq.py`'s ad-hoc parser, with the dialect's quoting, comments, identifiers, case folding, keywords as reserved words, and operator precedence tables; round-trip tests (parse, print, parse).
  **Status: PARTIAL.** The frontend is `tools/spec/sql2coq.py` (lexer and parser with the quoting, comments, executable comments, keywords and precedence of each family: `ENGINE`); `tools/spec/sqlprint.py` prints its syntax trees back to SQL and checks the round trip parse = parse . print . parse: OceanBase suite 924/924, PostgreSQL regression tests 1137/1137, MySQL `mysql-test` 49096/49097 of the printed queries (the one left: a set operation nested on the left inside a scalar subquery, printed with a leading parenthesis); CI runs it on `tools/spec/roundtrip_samples.sql`. The round trip found three parser gaps, fixed: parenthesised joins, derived tables and `IN` subqueries whose query starts with a parenthesised operand. Open: the printer of window calls, typed casts, table functions, grouping sets; an OCaml frontend for the extracted interpreter.
- **7.2 Result printer**: dialect-specific text output of values (so the conformance harness compares engine output text, not values converted by hand).
  **Status: DONE** (`src/data/dialects/ResultText.v`: `result_text d v`, the text of a value as the client of the dialect prints it: the NULL of `psql`, `sqlite3`, SQL*Plus and `mysql`, the booleans of `psql`; the other values by the engines' output functions in `text_of`; tests in `src/testing/Test_ResultText.v`).
- **7.3 Documentation**: `docs/DIALECTS.md` per-dialect sections generated from the model's tables; `docs/functions/*.md` (2.11); a "how to add a dialect" guide; a "how to read a semantic rule" guide with one worked example from query text to value.
  **Status: DONE.** `docs/guides/ADD_A_DIALECT.md`, `docs/guides/READING_A_RULE.md` (a worked example from `SELECT 1 / 0` to its value in two dialects), `docs/functions/*.md`, `docs/closeouts/*.md` (generated from the engines and the model), and `docs/DIALECT_TABLES.md`: every construct and every function name per dialect, computed by Coq from the dialect records (`tools/docs/gen_dialect_tables.py`).
- **7.4 Provenance**: each modelled behaviour carries a citation (file and line of the engine source at a recorded commit, or manual section); a script lists behaviours without citations; the checklist item "provenance" is complete when the list is empty.
- **7.5 Pull-request discipline**: one pull request per item; each PR description lists what was verified and how; unresolved questions recorded as marked-unresolved entries in `docs/OPEN_ISSUES.md`; comment on PR #1 after each merge.
- **7.6 Release of results**: a summary table (dialects by features) and a conformance dashboard page generated from the build, so progress is visible without reading the code.

---------------------------------------------------------------------------------------------------------

## Order of execution

1. Phase 1.1 (errors), 1.10 (session parameters), 1.2.1 (decimal scale), 1.3 (collations), 1.2.3/1.2.2 (integers, floats), 1.4, 1.8, 1.5, 1.6, 1.7, 1.9.
2. In parallel with 1: 5.1 (translator coverage) and 5.2 (MySQL-family suites): they need no value changes and find defects early; 3.1–3.5.
3. Phase 2 family by family (2.1, 2.2, 2.3, 2.5, 2.6, then 2.7, 2.4, 2.8, 2.9), each followed by its Phase 5 validation.
4. Phase 3 remainder (3.6–3.11), then Phase 4 closeouts dialect by dialect (4.1 PostgreSQL, 4.2 MySQL, 4.7 SQLite, 4.3 MariaDB, 4.4 TiDB, 4.8 OceanBase MySQL, 4.5 Percona, 4.6 PolarDB, 4.9 OceanBase Oracle, 4.10, 4.11).
5. Phase 6 (6.1–6.7) once the value model is stable; Phase 7 throughout.

Stop condition: every item of `docs/CHECKLIST.md` is `[x]` or is marked out of scope with a reason accepted by the user, and each dialect's conformance table in `docs/CONFORMANCE.md` has no unexplained failure.
