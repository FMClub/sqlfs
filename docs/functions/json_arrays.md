# JSON and array functions (TODO 1.6 and 2.8)

Code:
- `src/data/proof_of_concept/Json.v`: syntax, parser, normalization, paths, containment (TODO 1.6).
- `src/data/dialects/JsonFuns.v`: updates by path, removal, arrays, merges, depth, search, pretty
  printing, the `jsonb` operators of PostgreSQL (TODO 2.8).
- `Values.v` and `PostgreSQL.v`: PostgreSQL arrays.

Tests: `src/testing/Test_Json.v` and `src/testing/Test_JsonFuns.v`. The expected values of 2.8 are the
examples of the manuals.

## JSON

| Function | MySQL family | PostgreSQL | SQLite |
|---|---|---|---|
| construction, extraction, `->`, `->>`, `#>`, `@>`, `?`, type, length, valid, unquote, contains | M (1.6) | M (1.6) | M (1.6) |
| `json_set`, `json_insert`, `json_replace` | M | `jsonb_set` (create missing or not) M | M |
| `json_remove` / `#-` | M (several paths) | M (`#-` with a text-array path) | M |
| `json_array_append`, `json_array_insert` | M | `jsonb_insert` M (before or after) | — |
| `json_merge_patch` / `json_patch`, `json_merge_preserve` / `json_merge` | M (RFC 7396; preserve merges keys into arrays) | `||` M (objects merged, arrays concatenated) | `json_patch` M |
| `jsonb - key`, `jsonb - index`, `?|`, `?&` | — | M | — |
| `json_depth`, `json_contains_path`, `json_search`, `json_overlaps` | M (`json_search` without `LIKE` wildcards) | — | — |
| `json_pretty` / `jsonb_pretty` | M (two spaces) | M (four spaces) | — |
| `json_strip_nulls`, `jsonb_strip_nulls` | — | M | — |
| `json_quote`, `json_group_array`, `json_group_object` | — | — | M |
| `JSON_ARRAYAGG`, `JSON_OBJECTAGG`, `json_agg`, `json_object_agg` | M (2.5) | M (2.5) | — |
| SQL/JSON path (`jsonb_path_query`, `JSON_TABLE`, `json_each`, `json_object_keys`) | X | X | X | 

The last row is not modelled. Its functions use the SQL/JSON path language or return a table (Phase 3: table functions).

## Arrays (PostgreSQL)

An array is a `Value_J` of kind 2, holding the JSON array of its elements. It prints as `{1,2,NULL}`; an element is quoted when it is empty or `NULL`, or contains a space, a brace, a comma, a quote or a backslash (`array_out`). Two arrays compare element by element; a NULL element is greater than the others, and a proper prefix is smaller (`array_cmp`). The arrays have one dimension, with indexes starting at 1.

| Construct | Status |
|---|---|
| `ARRAY[e, …]`, `a[i]`, `a[i:j]`, `array_agg` | M |
| `array_length`, `cardinality`, `array_lower`, `array_upper`, `array_ndims`, `array_dims` | M |
| `array_append`, `array_prepend`, `array_cat`, `||` (array/array, array/element, element/array) | M |
| `array_position`, `array_positions` (`IS NOT DISTINCT FROM`), `array_remove`, `array_replace` | M |
| `array_to_string` (with a NULL text), `string_to_array` (NULL separator: one character per element; a NULL text) | M |
| `x op ANY (array)`, `x op ALL (array)` | M (three-valued) |
| `@>`, `<@`, `&&` | M |
| `unnest`, `generate_subscripts` | X (they return tables: Phase 3) |
| multidimensional arrays, array literals `'{1,2}'::int[]` | X (not modelled) |

MySQL, SQLite and Oracle mode have no SQL arrays in scalar contexts: JSON arrays play that part.
