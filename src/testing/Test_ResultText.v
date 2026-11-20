(** * The text of results per client (TODO 7.2) *)
Require Import List String ZArith.
Require Import Values Dialects PostgreSQL MySQL SQLite OceanBase ResultText.
Open Scope string_scope.
Ltac check := vm_compute; reflexivity.
Import NullValues.
Example null_texts :
  (result_text PostgreSQL (Value_Z None), result_text MySQL (Value_Z None), result_text SQLite (Value_Z None),
   result_text OceanBaseOracle (Value_Z None)) = (""%string, "NULL"%string, ""%string, ""%string).
Proof. check. Qed.
Example bool_texts :
  (result_text PostgreSQL (Value_bool (Some true)), result_text MySQL (Value_bool (Some true))) = ("t"%string, "1"%string).
Proof. check. Qed.
Example decimal_text : result_text MySQL (VDec (Qcanon.Q2Qc (QArith_base.Qmake 125 100)) 0 2) = "1.25".
Proof. check. Qed.
