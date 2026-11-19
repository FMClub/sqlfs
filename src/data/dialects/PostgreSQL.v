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
          (table_of_list (filter (fun p => negb (String.eqb (fst p) "group_concat")) aggregate_table))
          is_null
          bool3_of_value
          value_of_bool3
          sql_eq3
          sql_order
          canon_numeric
          false
          (fun f => match f with F_Bare_Column => false | _ => true end).
