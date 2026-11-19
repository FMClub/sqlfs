# Arithmetic and mathematical functions (TODO 2.1)

Status of each function per dialect: **M** modelled, **X** excluded (reason given), **—** the engine has no
such function. "MySQL" covers MySQL, Percona, PolarDB and OceanBase (MySQL mode); MariaDB and TiDB share
its table unless a note says otherwise. Tests: `src/testing/Test_Math.v`, `Test_Float.v`, `Test_Decimal.v`,
`Test_Integer.v`.

## How the values are computed

- **Doubles.** The C library functions which the engines call (`sqrt`, `cbrt`, `exp`, `log`, `log10`, `log2`,
  `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2`, `sinh`, `cosh`, `tanh`, `pow`) are computed exactly in
  fixed point (256 fractional bits, `IEEE.v`: series of `atanh`, `exp`, `sin`/`cos`, Machin's formula for
  `pi`; exact integer square and cube roots with a sticky bit) and rounded once to the nearest binary64.
  glibc's functions are correctly rounded for these inputs, except possibly in rare cases within a hair of a
  tie, which the model does not distinguish.
- **Compositions in C.** Where the engine composes two rounded operations, the model does too:
  MySQL `LOG2(x)` = `log(x) / M_LN2`, `LOG(b, x)` = `log(x) / log(b)`, `COT(x)` = `1.0 / tan(x)`,
  `DEGREES`/`RADIANS` multiply by the double `180 / M_PI` or `M_PI / 180` (`Item_func_units`);
  SQLite `degrees(x)` = `x * 180.0 / M_PI`, `log(b, x)` = `log(x) / log(b)`; PostgreSQL `degrees(x)` divides by
  the double `RADIANS_PER_DEGREE`.
- **PostgreSQL `numeric`.** `sqrt`, `exp`, `ln`, `log`, `log10` of a `numeric` give a `numeric` whose scale is
  computed as in `numeric.c` (`numeric_sqrt`, `numeric_exp`, `numeric_ln`, `log_var`,
  `estimate_ln_dweight`): at least 16 significant digits, not below the scale of the argument; rounded
  ties away from zero. An integer argument takes the `double precision` version (the preferred type).

## Table

| Function | PostgreSQL | MySQL family | SQLite | Source |
|---|---|---|---|---|
| `+ - * /`, `%`/`mod`, `div` | M | M | M | `Values.v`, `ValueKit.v` (Phase 1.2) |
| `abs`, `sign` | M | M | M (`sign` 3.44+) | `int.c`, `item_func.cc`, `func.c` |
| `ceil`/`ceiling`, `floor` | M | M | M (integer kept, REAL gives REAL) | `numeric.c`, `item_func.cc`, `func.c` (`ceilingFunc`) |
| `round`, `trunc`/`truncate` | M | M | M (`round`; `trunc`) | Phase 1.2 |
| `sqrt` | M (error < 0; `numeric` version) | M (NULL < 0) | M (NULL < 0) | `float.c` `dsqrt`, `numeric_sqrt`; `Item_func_sqrt`; `mathFunc` |
| `cbrt` | M | — | — | `float.c` `dcbrt` |
| `exp` | M (overflow/underflow errors; `numeric`) | M (overflow error) | M (Inf) | `dexp`, `numeric_exp`; `Item_func_exp`; `mathFunc` |
| `ln` | M (errors at 0 and < 0; `numeric`) | M (NULL) | M (NULL) | `dlog1`, `numeric_ln`; `Item_func_ln` |
| `log(x)` | M (base 10; `numeric`) | M (natural log) | M (base 10) | `dlog10`, `numeric_log`; `Item_func_log`; `logFunc` |
| `log(b, x)` | M (`numeric` only) | M | M (NULL for b <= 1) | `log_var`; `Item_func_log`; `logFunc` |
| `log2` | — | M | M | `Item_func_log2`; `logFunc` |
| `log10` | M | M | M | |
| `sin cos tan cot` | M (`cot` too; infinite argument is an error) | M (`cot(0)` out of range) | M (no `cot`) | `float.c`; `item_func.cc` |
| `asin acos atan` | M (out of [-1,1] is an error) | M (NULL) | M (NULL) | |
| `atan2`, `atan(y, x)` | M | M | M | |
| `sinh cosh tanh` | M | — | M | `float.c`; `mathFunc` |
| `pi()` | M | M (6 decimals: `3.141593`) | M | `Item_func_pi` |
| `degrees`, `radians` | M | M | M | see above |
| `power`/`pow` | M (`double` unless an argument is `numeric`) | M (non-finite result is an error) | M (NaN is NULL) | `dpow`; `Item_func_pow`; `mathFunc` |
| `& \| ~ << >>`, xor (`#` / `^`) | M (type of the operands; shifts wrap as C) | M (64-bit unsigned; shift >= 64 gives 0) | M (64-bit signed; negative shift reverses) | `int.c`; `Item_func_bit`; `OP_ShiftLeft` |
| `bit_count` | — | M | — | `Item_func_bit_count` |
| `gcd`, `lcm` | M (integers and `numeric`; `lcm` overflow is an error) | — | — | `int4gcd`, `numeric_gcd` |
| `factorial` | M (`numeric`; error < 0) | — | — | `numeric_fac` |
| `width_bucket` | M (exact arithmetic) | — | — | `width_bucket_numeric`, `width_bucket_float8` |
| `rand(N)` | — | M (first number of the sequence seeded with N) | — | `my_rnd_init`, `my_rnd` |
| `to_number` (Oracle mode) | — | — | — | M in `OceanBaseOracle`: the strict conversion (`ORA-01722` otherwise); with a format model, `,` and `$` are removed first (`Test_OracleForms.v`) |
| `rand()`, `random()` | X | X | X | not deterministic: the result is a set of values, which the deterministic model does not represent; an error "nondeterministic function" |
| `setseed` | X | — | — | session state |

## Known differences

- `RAND(N)` in a query over several rows: the engine's generator advances at each row; the model, whose
  functions have no state, gives every row the first number.
- `width_bucket` of doubles is computed exactly, while PostgreSQL computes it in double arithmetic; the
  bucket can differ when the operand lies within a rounding error of a bucket boundary.
- MySQL bit operators on binary strings (byte-wise in MySQL 8) are not modelled: the argument is taken as a
  number.
- OceanBase Oracle mode (`NUMBER` results with 38–40 significant digits for `SQRT`, `LN`, `EXP`, ...) is not
  yet modelled: Phase 4.
