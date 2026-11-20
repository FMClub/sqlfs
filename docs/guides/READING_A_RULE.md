# How to read a semantic rule: `SELECT 1 / 0`

This follows one query from its text to its value in two dialects.

## 1. From the text to the syntax

`tools/spec/sql2coq.py` (or a test written by hand) produces the query of `SqlFullSyntax.v`:

```coq
select_full Set_All (s_list [as_ (fn "/" [int 1; int 0]) (Attr_Z "c0")]) [] c_true g_fine c_true
```

`fn "/" [...]` is `E_Fun (Symbol "/") [...]`: the core knows no arithmetic, only the name of a function
symbol applied to expressions.

## 2. The core: `eval_sexpr` (`src/data/sql/SqlFull.v`)

The case `E_Fun f l` evaluates the arguments, returns the first failed argument if there is one
(`first_error`), and otherwise calls `interp_symbol T f vs`: the meaning of `/` is not in the core but in the
instance `T` of the values, built from the dialect.

## 3. The dialect: the table entry of `/`

`dialect_of d` makes `interp_symbol` look the name up in `vs_symb d`:

- **MySQL** (`src/data/dialects/MySQL.v`, `my_symbol_table_raw`): `("/", div)`. `div` converts the operands
  with the MySQL rules (a string prefix is read as a number), returns a `DECIMAL` whose scale is the scale of
  the dividend plus `div_precision_increment` (4), and **NULL** for a zero divisor: in a `SELECT`, MySQL
  turns `ERROR_FOR_DIVISION_BY_ZERO` into a warning.
- **PostgreSQL** (`src/data/proof_of_concept/Values.v`, `symbol_table_raw`): integer division of two
  integers, and `Value_Err "division by zero"` for a zero divisor.

## 4. The result

`eval_query_result` (`SqlFull.v`) turns a row holding a `Value_Err` into a failed query. So the same query is
the row `NULL` in MySQL and the error `division by zero` in PostgreSQL; `src/testing/Test_Dialects.v` (`div_zero`) checks
both. The provenance of each behaviour is in the row of `/` in `docs/functions/core.md`.

## Reading any rule

1. Find the construct in `SqlFull.v` (`squery`, `sfrom`, `sexpr`, `scond`, `swfun`) and its case in the
   evaluation functions (`eval_squery`, `eval_sfrom`, `eval_sexpr`, `eval_scond`, `eval_window`).
2. When the case calls `interp_symbol`, `interp_predicate`, `interp_aggregate` or a field of `dialect`
   (`canon`, `order`, `eq3`, `truth_of_value`, `supports`, ...), the meaning is in the dialect: look the name up
   in its tables (`docs/functions/INDEX.md` lists the file which defines each name).
3. The tests named in the comments, and `docs/closeouts/ENGINE.md`, say what was checked and against what.
