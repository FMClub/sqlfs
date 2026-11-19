# Functions added by the dialect closeouts (TODO 4.1-4.8)

Status: **M** modelled. Tests: `src/testing/Test_Closeout.v`. The full catalogues are in `docs/closeouts/`.

| Function | Dialect | Status | Source and notes |
|---|---|---|---|
| `scale`, `min_scale`, `trim_scale` | PostgreSQL | M | `numeric.c` (`numeric_scale`, `numeric_min_scale`, `numeric_trim_scale`): the scale, the least scale which represents the value exactly, the value with that scale; an integer argument has scale 0 |
| `to_bin`, `to_oct` | PostgreSQL | M | `varlena.c` (`to_bin32`, `to_oct64`, ...): the two's complement of the 32- or 64-bit integer, like `to_hex` |
| `array_reverse`, `trim_array` | PostgreSQL | M | `array_userfuncs.c`: the elements in reverse order; the array without its last `n` elements (an error when `n` is negative or larger than the length) |
| synonyms `character_length`, `textlen`, `dexp`, `dlog10`, `dlog1`, `dround`, `dtrunc`, `dsqrt`, `dcbrt`, `dpow`, `pow`, `numeric_exp`, `numeric_ln`, `numeric_log`, `numeric_sqrt`, `numeric_div_trunc` | PostgreSQL | M | `pg_proc.dat`: other names of the same C functions (`pg_aliases` in `PostgreSQL.v`) |
| `conv`, `bin`, `oct` | MySQL family | M | `item_strfunc.cc` (`Item_func_conv`): the longest prefix in base `from` (2 to 36), 64-bit unsigned; a negative `to` gives a signed result; `BIN (n)` is `CONV (n, 10, 2)`, `OCT (n)` is `CONV (n, 10, 8)` |
| `crc32` | MySQL family | M | zlib's CRC-32 of the bytes of the string (polynomial `0xEDB88320`) |
| `inet_aton`, `inet_ntoa`, `is_ipv4` | MySQL family | M | `item_inetfunc.cc`: `'127.1'` is `127.0.0.1` (the last part is the low byte); `IS_IPV4` needs four parts |
| `quote` | MySQL family | M | `Item_func_quote`: `'`, `\`, NUL and `^Z` escaped by a backslash; NULL gives the text `NULL` |
| `any_value` | MySQL family | M | the value of its argument (it only lifts `ONLY_FULL_GROUP_BY`) |
| `make_set`, `export_set` | MySQL family | M | `Item_func_make_set`, `Item_func_export_set`: the strings of the bits set (NULLs skipped); `on`/`off` for the first `n` bits (64 by default) |
| `weekofyear` | MySQL family | M | `WEEK (d, 3)`: the ISO 8601 week |
| synonyms `lcase`, `ucase`, `character_length`, `time`, `timestamp` (one argument), `timestamp_diff`, `localtime`, `localtimestamp` | MySQL family | M | `my_aliases` in `MySQL.v` |
