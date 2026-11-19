# String functions (TODO 2.2)

Status per dialect: **M** modelled, **X** excluded (reason), **—** the engine has no such function.
"MySQL" is the MySQL family (MySQL, MariaDB, TiDB, Percona, PolarDB, OceanBase MySQL mode); "Oracle" is
OceanBase in Oracle mode. Code: `src/data/dialects/StringFuns.v` (algorithms on code points, wrappers
parameterized by the argument conversions of each dialect), `src/data/proof_of_concept/Hash.v` (digests,
hexadecimal, Base64). Tests: `src/testing/Test_String.v` (the expected values are the examples of the
engines' manuals).

## Conventions

- Texts are UTF-8; positions and lengths count characters, except MySQL `LENGTH`/`OCTET_LENGTH`,
  `ASCII`, `HEX` (bytes).
- The argument conversions are the dialect's: MySQL and SQLite convert numbers to their text (a SQLite
  `REAL` with `%!.15g`); Oracle mode reads `''` as NULL and returns NULL for an empty result.
- Comparisons inside `FIELD`, `FIND_IN_SET`, `STRCMP` and `LIKE` of the MySQL family use the session
  collation (TODO 1.3).

## Table

| Function | PostgreSQL | MySQL | SQLite | Oracle | Source / notes |
|---|---|---|---|---|---|
| `lpad`, `rpad` | M (cut; empty pad leaves the string) | M (empty pad → NULL; n < 0 → NULL) | — | M (space by default) | `varlena.c` `lpad`; `Item_func_lpad` |
| `substring_index` | — | M | — | — | `Item_func_substr_index` |
| `split_part` | M (negative position, PG 14; 0 is an error) | — | — | — | `split_part` |
| `translate` | M | — | — | M | `oracle_compat.c` `translate` |
| `initcap` | M | — | — | M | words are runs of letters and digits |
| `overlay … placing … from … for` | M | — | — | — | SQL standard syntax translated |
| `position(a in b)`, `strpos` | M | M (= `LOCATE`) | — | — | |
| `instr` | — | M (existing) | M (characters) | M (existing) | |
| `trim([leading\|trailing\|both] r from s)` | M (set of characters) | M (**string** `r` removed repeatedly) | M (set) | M (set) | `Item_func_trim` vs `btrim` |
| `btrim`, `ltrim(s, set)`, `rtrim(s, set)` | M | — (one-argument forms only) | M | M | |
| `concat_ws` | M (skips NULL) | M (existing) | M | — | |
| `quote_literal`, `quote_ident` | M (`E'…'` with backslashes; reserved words quoted) | — | — | — | `quote.c`, `ruleutils.c` `quote_identifier` |
| `quote` | — | — | M | — | `quoteFunc` |
| `format` | M (`%s %I %L %%`, `%n$`; widths are an error) | M (`FORMAT(x, d)`: grouping by 3 with `,`, en_US) | X (`printf`-style, not modelled) | — | `varlena.c` `text_format`; `Item_func_format` |
| `md5` | M | M | — | — | RFC 1321 |
| `sha1`/`sha`, `sha2(s, n)` | X (`sha256(bytea)` returns `bytea`, not modelled) | M (224/256/384/512; 0 = 256) | — | — | FIPS 180-4 |
| `hex`, `unhex` | — (`to_hex(int)` M) | M (number: digits of the integer; text: bytes, upper case) | M (`hex` of the text, NULL → `''`) | — | |
| `to_base64`, `from_base64` | — | M (invalid → NULL) | — | — | RFC 4648 |
| `soundex` | — (extension `fuzzystrmatch`) | M (not cut to 4 characters) | — (compile-time option) | — | `Item_func_soundex` |
| `space`, `insert`, `elt`, `field`, `find_in_set` | — | M | — | — | |
| `ascii` | M (code point) | M (first byte) | — | M | |
| `ord`, `char(n, …)` | — | M | M (`char`: code points) | — | |
| `chr` | M (0, negatives, surrogates are errors) | — | — | M (bytes) | |
| `unicode` | — | — | M | — | |
| `octet_length`, `bit_length` | M | M | M (`octet_length`) | — | |
| `strcmp` | — | M (session collation) | — | — | |
| `like … escape e` | M (`''` disables) | M | M (case-insensitive ASCII) | M | an escape of several characters is an error |
| `ilike` | M (ASCII lower case) | — | — | — | |
| `similar to`, `regexp_*` | → TODO 2.4 | → 2.4 | → 2.4 | → 2.4 | |

## Known differences

- `upper`/`lower`/`initcap`/`ILIKE` fold the case of ASCII letters only. The engines fold all of
  Unicode (MySQL by the collation, PostgreSQL by the locale or ICU, Oracle by the character set). Unicode
  case mapping needs generated tables, like `CollationData.v`. This is recorded in `docs/OPEN_ISSUES.md`.
- MySQL `FORMAT(x, d)` of a `DOUBLE` rounds the exact value of the double. MySQL rounds the double with
  `my_double_round`, and the results can differ by one unit in the last place when the value is within
  one rounding error of a tie.
- `CHAR(n USING charset)` and the binary-string forms of MySQL functions (`HEX` of `BINARY`, bitwise
  operators on strings) are not modelled.
- PostgreSQL text functions accept only text arguments (an `integer` argument is an error, "function does
  not exist"). The model converts the argument to its text, as the MySQL family does. Argument type
  checking is TODO 2.10.
