(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Tests of the truth values of the dialects (TODO 1.4).                         *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String ZArith NArith.

Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.

Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax
        Dialects ValueKit PostgreSQL MySQL SQLite OceanBase SpecRunner.

Import Tuple.
Import ListNotations.
Open Scope string_scope.

Ltac check := vm_compute; reflexivity.

Definition result (d : vsem) (e : sexpr) : string :=
  match eval_query_result ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) 
                          (to_dialect d (select_where [as_ (int 1) (Attr_Z "c0")] [] (c_expr e))) with
  | QR_Error _ => "error"
  | QR_Rows _ nil => "false or unknown"
  | QR_Rows _ _ => "true"
  end.

(** [WHERE e] for a value [e]:
    - PostgreSQL: a boolean, or a string which is a boolean literal; anything else is a type error;
    - MySQL and SQLite: the value is read as a number, its prefix for a string; 0 is false. *)
Example where_int : 
  map (fun d => result d (int 1)) [PostgreSQL; MySQL; SQLite] = ["error"; "true"; "true"].
Proof. check. Qed.

Example where_text_true : 
  map (fun d => result d (str "true")) [PostgreSQL; MySQL; SQLite] = ["true"; "false or unknown"; "false or unknown"].
Proof. check. Qed.

Example where_text_number : 
  map (fun d => result d (str "1abc")) [PostgreSQL; MySQL; SQLite] = ["error"; "true"; "true"].
Proof. check. Qed.

Example where_half : 
  map (fun d => result d (cst (VD 5 1))) [PostgreSQL; MySQL; SQLite] = ["error"; "true"; "true"].
Proof. check. Qed.

Example where_null : 
  map (fun d => result d (cst NullZ)) [PostgreSQL; MySQL; SQLite] = ["false or unknown"; "false or unknown"; "false or unknown"].
Proof. check. Qed.
