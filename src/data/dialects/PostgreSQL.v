(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**                          The PostgreSQL dialect                                 *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String ZArith NArith QArith Qcanon.

Require Import Bool3 OrderedSet SqlFull Values Dialects ValueKit.

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
(** [substr] is a synonym of [substring] *)
Definition pg_symbol_table : list (string * (list value -> value)) :=
  match string_assoc _ "substring" symbol_table with
  | Some f => ("substr", f) :: symbol_table
  | None => symbol_table
  end.

Definition PostgreSQL : vsem :=
  mk_vsem "PostgreSQL"
          (table_of_list predicate_table)
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
          (fun _ _ => false)
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
