# Functions added by the dialect closeouts (TODO 4.1-4.8)

Status: **M** modelled. Tests: `src/testing/Test_Closeout.v`. The full catalogues are in `docs/closeouts/`.

| Function | Dialect | Status | Source and notes |
|---|---|---|---|
| `scale`, `min_scale`, `trim_scale` | PostgreSQL | M | `numeric.c` (`numeric_scale`, `numeric_min_scale`, `numeric_trim_scale`): the scale, the least scale which represents the value exactly, the value with that scale; an integer argument has scale 0 |
| `to_bin`, `to_oct` | PostgreSQL | M | `varlena.c` (`to_bin32`, `to_oct64`, ...): the two's complement of the 32- or 64-bit integer, like `to_hex` |
| `array_reverse`, `trim_array` | PostgreSQL | M | `array_userfuncs.c`: the elements in reverse order; the array without its last `n` elements (an error when `n` is negative or larger than the length) |
| synonyms `character_length`, `textlen`, `dexp`, `dlog10`, `dlog1`, `dround`, `dtrunc`, `dsqrt`, `dcbrt`, `dpow`, `pow`, `numeric_exp`, `numeric_ln`, `numeric_log`, `numeric_sqrt`, `numeric_div_trunc` | PostgreSQL | M | `pg_proc.dat`: other names of the same C functions (`pg_aliases` in `PostgreSQL.v`) |
