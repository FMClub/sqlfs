(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   The number of arguments of the functions of each dialect (TODO 2.10): a call  *)
(**   with another number of arguments is rejected (acceptance) and is an error     *)
(**   (evaluation). The ranges are those of the manuals.                            *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String.

Import ListNotations.
Open Scope string_scope.

(** a function, its minimal number of arguments and its maximal one ([None]: unbounded) *)
Definition arity := (string * nat * option nat)%type.

Definition fixed (n : string) (k : nat) : arity := (n, k, Some k).
Definition range (n : string) (a b : nat) : arity := (n, a, Some b).
Definition atleast (n : string) (a : nat) : arity := (n, a, None).

(** shared by the dialects which have the function with this arity *)
Definition common_arities : list arity :=
  map (fun n => fixed n 1) ["abs"; "sign"; "floor"; "ceil"; "ceiling"; "sqrt"; "exp"; "ln"; "log10"; "sin"; "cos"; "tan";
                            "asin"; "acos"; "degrees"; "radians"; "upper"; "lower"; "reverse"; "length"; "char_length";
                            "octet_length"; "md5"; "ascii"; "initcap"]
  ++ map (fun n => fixed n 2) ["atan2"; "nullif"; "left"; "right"; "repeat"; "ifnull"; "nvl"; "datediff"]
  ++ [fixed "pi" 0; fixed "replace" 3; range "substr" 2 3; range "substring" 2 3; range "round" 1 2; atleast "coalesce" 1].

Definition mysql_arities : list arity :=
  [range "log" 1 2; fixed "log2" 1; fixed "cot" 1; range "atan" 1 2; fixed "power" 2; fixed "pow" 2; fixed "mod" 2;
   fixed "truncate" 2; range "rand" 0 1; atleast "greatest" 2; atleast "least" 2; fixed "if" 3; atleast "concat" 1;
   atleast "concat_ws" 2; fixed "trim" 1; fixed "ltrim" 1; fixed "rtrim" 1; range "mid" 2 3; range "locate" 2 3;
   fixed "instr" 2; fixed "lpad" 3; fixed "rpad" 3; fixed "substring_index" 3; fixed "insert" 4; fixed "space" 1;
   atleast "elt" 2; atleast "field" 2; fixed "find_in_set" 2; fixed "soundex" 1; fixed "sha1" 1; fixed "sha" 1;
   fixed "sha2" 2; fixed "hex" 1; fixed "unhex" 1; fixed "to_base64" 1; fixed "from_base64" 1; fixed "ord" 1;
   atleast "char" 1; range "format" 2 3; fixed "strcmp" 2; fixed "bit_count" 1;
   range "regexp_like" 2 3; range "regexp_instr" 2 6; range "regexp_substr" 2 5; range "regexp_replace" 3 6;
   atleast "json_extract" 2; atleast "json_set" 3; atleast "json_insert" 3; atleast "json_replace" 3;
   atleast "json_remove" 2; atleast "json_array_append" 3; atleast "json_array_insert" 3;
   atleast "json_merge_patch" 2; atleast "json_merge_preserve" 2; atleast "json_merge" 2; range "json_depth" 1 1;
   atleast "json_contains_path" 3; range "json_search" 3 5; fixed "json_overlaps" 2; fixed "json_pretty" 1;
   range "json_contains" 2 3; range "json_length" 1 2; fixed "json_type" 1; fixed "json_valid" 1; fixed "json_unquote" 1;
   fixed "json_quote" 1; range "json_keys" 1 2;
   fixed "date_format" 2; fixed "str_to_date" 2; fixed "makedate" 2; fixed "maketime" 3; fixed "sec_to_time" 1;
   fixed "time_to_sec" 1; fixed "from_days" 1; fixed "to_days" 1; range "from_unixtime" 1 2; fixed "dayname" 1;
   fixed "monthname" 1; fixed "period_add" 2; fixed "period_diff" 2; fixed "timediff" 2; fixed "addtime" 2;
   fixed "subtime" 2; fixed "time_format" 2; fixed "timestampdiff" 3; fixed "last_day" 1; range "week" 1 2;
   fixed "weekday" 1; fixed "dayofweek" 1; fixed "dayofmonth" 1; fixed "dayofyear" 1; fixed "quarter" 1;
   fixed "year" 1; fixed "month" 1; fixed "day" 1; fixed "hour" 1; fixed "minute" 1; fixed "second" 1;
   fixed "microsecond" 1; range "unix_timestamp" 0 1; fixed "date" 1; fixed "isnull" 1; atleast "interval_index" 2;
   fixed "version" 0; fixed "database" 0; fixed "schema" 0; fixed "user" 0; fixed "current_user" 0;
   fixed "session_user" 0; fixed "system_user" 0; fixed "connection_id" 0; range "last_insert_id" 0 1;
   fixed "row_count" 0; fixed "found_rows" 0].

(** MariaDB: [REGEXP_*] take only the text and the pattern (and the replacement); [LPAD] and [RPAD] have
    an optional padding (a space by default) *)
Definition mariadb_arities : list arity :=
  [fixed "regexp_instr" 2; fixed "regexp_substr" 2; fixed "regexp_replace" 3; range "lpad" 2 3; range "rpad" 2 3].

Definition pg_arities : list arity :=
  [range "log" 1 2; fixed "cbrt" 1; fixed "cot" 1; fixed "atan" 1; fixed "power" 2; fixed "mod" 2; range "trunc" 1 2;
   fixed "div" 2; fixed "gcd" 2; fixed "lcm" 2; fixed "factorial" 1; fixed "width_bucket" 4; fixed "random" 0;
   atleast "greatest" 1; atleast "least" 1; atleast "concat" 1; atleast "concat_ws" 1; range "lpad" 2 3;
   range "rpad" 2 3; fixed "split_part" 3; fixed "translate" 3; range "overlay" 3 4; fixed "strpos" 2;
   fixed "position" 2; range "btrim" 1 2; range "ltrim" 1 2; range "rtrim" 1 2; range "trim" 1 1;
   fixed "quote_literal" 1; fixed "quote_ident" 1; atleast "format" 1; fixed "chr" 1; fixed "to_hex" 1;
   fixed "bit_length" 1; range "regexp_replace" 3 6; range "regexp_count" 2 4; range "regexp_instr" 2 7;
   range "regexp_substr" 2 6; range "regexp_like" 2 3; fixed "substring_regex" 2; range "age" 1 2; fixed "to_date" 2;
   range "to_timestamp" 1 2; fixed "make_time" 3; fixed "make_timestamp" 6; range "make_interval" 0 7;
   fixed "make_date" 3; fixed "date_bin" 3; fixed "justify_days" 1; fixed "justify_hours" 1;
   fixed "justify_interval" 1; fixed "isfinite" 1; fixed "date_trunc" 2; fixed "date_part" 2; fixed "to_char" 2;
   range "jsonb_set" 3 4; range "jsonb_insert" 3 4; fixed "jsonb_strip_nulls" 1; fixed "json_strip_nulls" 1;
   fixed "jsonb_pretty" 1; fixed "array_length" 2; fixed "cardinality" 1; fixed "array_append" 2;
   fixed "array_prepend" 2; fixed "array_cat" 2; range "array_position" 2 3; fixed "array_positions" 2;
   fixed "array_remove" 2; fixed "array_replace" 3; range "array_to_string" 2 3; range "string_to_array" 2 3;
   fixed "array_lower" 2; fixed "array_upper" 2; fixed "array_ndims" 1; fixed "array_dims" 1;
   atleast "num_nulls" 0; atleast "num_nonnulls" 0;
   fixed "version" 0; fixed "current_user" 0; fixed "session_user" 0; fixed "user" 0; fixed "current_role" 0;
   fixed "current_database" 0; fixed "current_catalog" 0; fixed "current_schema" 0; fixed "pg_backend_pid" 0].

Definition lite_arities : list arity :=
  [range "log" 1 2; fixed "log2" 1; fixed "pow" 2; fixed "power" 2; fixed "mod" 2; fixed "trunc" 1; fixed "instr" 2;
   range "trim" 1 2; range "ltrim" 1 2; range "rtrim" 1 2; fixed "hex" 1; range "unhex" 1 2; atleast "char" 0;
   fixed "unicode" 1; fixed "quote" 1; atleast "max_scalar" 2; atleast "min_scalar" 2; fixed "iif" 3;
   atleast "coalesce" 2; atleast "concat" 1; atleast "concat_ws" 1; fixed "likely" 1; fixed "unlikely" 1;
   fixed "likelihood" 2; atleast "json_set" 1; atleast "json_insert" 1; atleast "json_replace" 1;
   atleast "json_remove" 1; fixed "json_patch" 2; fixed "json_quote" 1; fixed "sqlite_version" 0;
   fixed "changes" 0; fixed "total_changes" 0; fixed "last_insert_rowid" 0].

Definition ora_arities : list arity :=
  [fixed "nvl2" 3; atleast "decode" 3; range "lpad" 2 3; range "rpad" 2 3; fixed "translate" 3; fixed "chr" 1;
   range "instr" 2 4; range "trunc" 1 2; fixed "add_months" 2; fixed "last_day" 1; fixed "months_between" 2;
   range "to_date" 1 2; range "to_char" 1 3; fixed "next_day" 2; range "ltrim" 1 2; range "rtrim" 1 2;
   range "regexp_count" 2 4; range "regexp_instr" 2 7; range "regexp_substr" 2 6; range "regexp_replace" 2 6;
   atleast "greatest" 1; atleast "least" 1; fixed "user" 0; range "sys_context" 2 3].

(** the table of a dialect, by its name ([vs_name]) *)
Definition arities_of (dialect : string) : list arity :=
  match dialect with
  | "PostgreSQL" => pg_arities ++ common_arities
  | "SQLite" => lite_arities ++ common_arities
  | "OceanBase (Oracle mode)" => ora_arities ++ common_arities
  | "MariaDB" => mariadb_arities ++ mysql_arities ++ common_arities
  | _ => mysql_arities ++ common_arities
  end.

(** a call of [f] with [n] arguments is well formed; a function which is not in the table is not checked *)
Definition arity_ok (dialect f : string) (n : nat) : bool :=
  match find (fun a => String.eqb (fst (fst a)) f) (arities_of dialect) with
  | Some (_, lo, hi) => Nat.leb lo n && match hi with Some h => Nat.leb n h | None => true end
  | None => true
  end.
