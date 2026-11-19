(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**                          The PostgreSQL dialect                                 *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String Ascii ZArith NArith QArith Qcanon.

Require Import Bool3 OrderedSet SqlFull Values Dialects ValueKit Collation Hash StringFuns.

Close Scope Q_scope.
Close Scope Qc_scope.
Open Scope string_scope.

Import NullValues.

(** The key of a value: all the NULLs are the same, and the numbers are compared as
    exact numerics, whatever their declared type. *)
Definition canon_numeric (v : value) : value :=
  match v with
  | Value_Z (Some z) => Value_Q (Some (Qc_of_Z z))
  | Value_I (Some (z, _)) => Value_Q (Some (Qc_of_Z z))
  (* [1.50] and [1.5] are not distinct: the scale is not part of the identity of a decimal *)
  | Value_D (Some (q, _, _)) => Value_Q (Some q)
  (* a finite float, or -0, is identified with the number it stands for *)
  | Value_F (Some (q, k)) => if Nat.leb (Nat.div (Nat.modulo k 10) 2) 1 then Value_Q (Some q) else Value_F (Some (q, (2 * Nat.div (Nat.modulo k 10) 2)%nat))
  | _ => if is_null v then Value_Z None else v
  end.

(** PostgreSQL:
    - strict typing: values of different types are not comparable (here the comparison
      is UNKNOWN, where PostgreSQL signals a type error);
    - conditions are booleans;
    - strings are compared byte by byte (the default deterministic collation);
    - NULLs are the largest values of [ORDER BY];
    - [/] on integers is the integer division, truncated towards zero; a division by zero
      is an error (here NULL);
    - [||] is the concatenation, and NULL if one of the operands is NULL; [concat]
      ignores NULLs;
    - [greatest] and [least] ignore NULLs;
    - [avg] of integers is an exact numeric, [sum] of the empty set is NULL.
    The tables are those of [Values.v]. *)
(** ** The string functions (TODO 2.2, [src/backend/utils/adt/varlena.c], [oracle_compat.c], [quote.c])

    The positions and lengths count characters. [lpad]/[rpad] cut a longer string and leave it when the
    padding is empty; [split_part] counts from the end for a negative position (PostgreSQL 14); [chr (0)] is
    an error; [to_hex] writes the two's complement of the integer in its width. *)
Definition pg_skit : skit :=
  mk_skit (fun v => match v with Value_C (Some (s, _)) => Some s | _ => text_of v end)
          (fun v => match int_parts v with Some (z, _) => Some z | None => None end)
          (fun s => Value_string (Some s)) (Value_string None).

Definition pg_string_table : list (string * (list value -> value)) :=
  let k := pg_skit in
     ("lpad", f_pad k true false) :: ("rpad", f_pad k false false)
  :: ("split_part", f_split_part k) :: ("translate", f_translate k)
  :: ("initcap", f_text1 k initcap_cp)
  :: ("overlay", f_overlay k)
  :: ("strpos", f_strpos k)
  :: ("position", fun l => match l with a :: b :: nil => f_strpos k (b :: a :: nil) | _ => Value_Err "wrong number of arguments" end)
  :: ("btrim", f_trim_set k 0) :: ("ltrim", f_trim_set k 1) :: ("rtrim", f_trim_set k 2)
  :: ("trim_both", f_trim_set k 0) :: ("trim_leading", f_trim_set k 1) :: ("trim_trailing", f_trim_set k 2)
  :: ("concat_ws", f_concat_ws k)
  :: ("md5", f_digest k md5)
  :: ("quote_literal", f_text1 k quote_literal_cp)
  :: ("quote_ident", f_text1 k quote_ident_cp)
  :: ("format", fun l => match l with
                         | f :: args => match sk_txt k f with
                                        | Some f => match pg_format_string (cps f) (map (fun v => option_map cps (sk_txt k v)) args) with
                                                    | Some r => ret_cp k r
                                                    | None => Value_Err "unrecognized format() type specifier"
                                                    end
                                        | None => Value_string None end
                         | nil => Value_Err "wrong number of arguments" end)
  :: ("ascii", fun l => match texts k l with
                        | Some (s :: nil) => Value_I (Some (match cps s with c :: _ => c | nil => 0 end, 32%nat))
                        | Some _ => Value_Err "wrong number of arguments"
                        | None => Value_I None end)
  :: ("chr", fun l => match l with
                      | v :: nil => match sk_int k v with
                                    | Some n => if Z.eqb n 0 then Value_Err "null character not permitted"
                                                else if Z.ltb n 0 then Value_Err "character number must be positive"
                                                else if Z.ltb 1114111 n || (Z.leb 55296 n && Z.leb n 57343)
                                                then Value_Err "requested character not valid for encoding"
                                                else Value_string (Some (txt (n :: nil)))
                                    | None => Value_string None end
                      | _ => Value_Err "wrong number of arguments" end)
  :: ("to_hex", fun l => match l with
                         | v :: nil => match int_parts v with
                                       | Some (z, w) => let b := if Nat.eqb w 64 then 64%nat else 32%nat in
                                                        let u := Z.modulo z (2 ^ Z.of_nat b) in
                                                        let h := hex_of_bytes false (bytes_be (Nat.div b 8) u) in
                                                        (* without the leading zeros *)
                                                        let fix strip (s : string) :=
                                                            match s with String "0"%char ((String _ _) as r) => strip r | _ => s end in
                                                        Value_string (Some (strip h))
                                       | None => Value_string None end
                         | _ => Value_Err "wrong number of arguments" end)
  :: ("octet_length", fun l => match texts k l with
                               | Some (s :: nil) => Value_I (Some (Z.of_nat (String.length s), 32%nat))
                               | _ => Value_I None end)
  :: ("num_nulls", fun l => VInt 32 (Z.of_nat (List.length (filter is_null l))))
  :: ("num_nonnulls", fun l => VInt 32 (Z.of_nat (List.length (filter (fun v => negb (is_null v)) l))))
  :: ("bit_length", fun l => match texts k l with
                             | Some (s :: nil) => Value_I (Some (8 * Z.of_nat (String.length s), 32%nat))
                             | _ => Value_I None end)
  :: nil.

(** ** Comparisons and conditionals (TODO 2.3): [BETWEEN SYMMETRIC] holds when [x] is between the two
    bounds in either order; [num_nulls] and [num_nonnulls] count the NULL arguments *)
Definition pg_between (l : list value) : bool3 :=
  match string_assoc _ "between" predicate_table with Some p => p l | None => unknown3 end.

Definition pg_extra_preds : list (string * (list value -> bool3)) :=
     ("between symmetric", fun l => match l with
                                    | x :: a :: b :: nil => orb3 (pg_between (x :: a :: b :: nil)) (pg_between (x :: b :: a :: nil))
                                    | _ => unknown3 end)
  :: ("not between symmetric", fun l => match l with
                                        | x :: a :: b :: nil => negb3 (orb3 (pg_between (x :: a :: b :: nil)) (pg_between (x :: b :: a :: nil)))
                                        | _ => unknown3 end)
  :: nil.

(** [substr] is a synonym of [substring] *)
Definition pg_symbol_table : list (string * (list value -> value)) :=
  pg_string_table ++
  match string_assoc _ "substring" symbol_table with
  | Some f => ("substr", f) :: symbol_table
  | None => symbol_table
  end.

Definition PostgreSQL : vsem :=
  mk_vsem "PostgreSQL"
          (table_of_list (like_table pg_skit false (fun c => c) low_cp (Some 92) ++ pg_extra_preds ++ predicate_table))
          (table_of_list pg_symbol_table)
          (table_of_list (filter (fun p => negb (String.eqb (fst p) "group_concat")) aggregate_table
                          ++ ("string_agg_sep", agg_concat_sep_by is_null "") :: nil))
          is_null
          (fun v => match v with
                    | Value_string (Some s) => match bool_of_string s with Some b => bool3_of_bool b | None => unknown3 end
                    | _ => bool3_of_value v end)
          value_of_bool3
          sql_eq3
          sql_order
          canon_numeric
          false
          (fun f => match f with F_Bare_Column | F_Fetch_Percent => false | _ => true end)
          false
          (* an escape of more than one character: [invalid escape string] *)
          (bad_escape pg_skit)
          (* an integer literal is an [integer] if it fits, a [bigint] if it fits, a [numeric] otherwise
             ([make_const] in [src/backend/parser/parse_node.c]) *)
          (fun v => match v with
                    | Value_Z (Some z) => if int_range_ok 32 z then VInt 32 z 
                                          else if int_range_ok 64 z then v else VDec (Qc_of_Z z) 0 0
                    | _ => v end)
          (* a condition must be a boolean ([coerce_to_boolean]): a string is read as a boolean literal
             (['true'], ['t'], ['yes'], ['1'], ...), another value is a type error *)
          (fun v => if is_null v then false
                    else match v with
                         | Value_bool _ => false
                         | Value_string (Some s) => match bool_of_string s with Some _ => false | None => true end
                         | _ => true end)
          (fun _ _ l => l).
