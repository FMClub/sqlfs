(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Tests of binary floating-point numbers (TODO 1.2.2).                          *)
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

Notation c0 := (Attr_Z "c0").

Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).

(** the text of the value of [e], as the dialect prints it *)
Definition text (d : vsem) (e : sexpr) : string :=
  match run d (select_where [as_ (fn "cast_string" [e]) c0] [] c_true) with
  | t :: nil => show_value (dot (TD d) t (out_attr 0))
  | _ => "?"
  end.

Definition fails (d : vsem) (e : sexpr) : bool :=
  match eval_query_result ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) 
                          (to_dialect d (select_where [as_ e c0] [] c_true)) with
  | QR_Error _ => true
  | _ => false
  end.

Definition d01 := cst (VFl false 1 (-1)).
Definition d02 := cst (VFl false 2 (-1)).

(** [0.1::float8 + 0.2::float8] is not [0.3] *)
Example pg_sum : text PostgreSQL (fn "+" [d01; d02]) = "0.30000000000000004".
Proof. check. Qed.

Example my_sum : text MySQL (fn "+" [d01; d02]) = "0.30000000000000004".
Proof. check. Qed.

(** SQLite prints 15 significant digits *)
Example lite_sum : text SQLite (fn "+" [d01; d02]) = "0.3".
Proof. check. Qed.

Example pg_third : text PostgreSQL (fn "/" [cst (VFl false 1 0); int 3]) = "0.3333333333333333".
Proof. check. Qed.

Example pg_big : text PostgreSQL (cst (VFl false 1 15)) = "1e+15".
Proof. check. Qed.

Example my_big : text MySQL (cst (VFl false 1 15)) = "1e15".
Proof. check. Qed.

Example lite_big : text SQLite (cst (VFl false 1 15)) = "1.0e+15".
Proof. check. Qed.

(** a binary32 [45.23] is [45.22999954223633] as a double *)
Example my_float32 : text MySQL (fn "+" [cst (VFl true 4523 (-2)); int 0]) = "45.22999954223633".
Proof. check. Qed.

Example pg_float4 : text PostgreSQL (cst (VFl true 4523 (-2))) = "45.23".
Proof. check. Qed.

(** in MySQL, a string in an arithmetic operation is a double *)
Example my_string_double : text MySQL (fn "+" [str "0.1"; str "0.2"]) = "0.30000000000000004".
Proof. check. Qed.

(** division by zero: an error in PostgreSQL, NULL in MySQL and SQLite *)
Example pg_div_zero : fails PostgreSQL (fn "/" [d01; int 0]) = true.
Proof. check. Qed.

Example my_div_zero : text MySQL (fn "/" [d01; int 0]) = "NULL".
Proof. check. Qed.

(** overflow: an error in PostgreSQL and MySQL *)
Example pg_overflow : fails PostgreSQL (fn "*" [cst (VFl false 1 308); int 10]) = true.
Proof. check. Qed.

Example my_overflow : fails MySQL (fn "*" [cst (VFl false 1 308); int 10]) = true.
Proof. check. Qed.

(** NaN and the infinities of PostgreSQL *)
Example pg_nan : text PostgreSQL (fn "cast_float8" [str "NaN"]) = "NaN".
Proof. check. Qed.

Example pg_inf_minus : text PostgreSQL (fn "-" [fn "cast_float8" [str "Infinity"]; fn "cast_float8" [str "Infinity"]]) = "NaN".
Proof. check. Qed.

(** [round(float8)] rounds ties to even ([rint]), [round(numeric)] away from zero *)
Example pg_rint : text PostgreSQL (fn "round" [cst (VFl false 25 (-1))]) = "2".
Proof. check. Qed.

Example pg_round_numeric : text PostgreSQL (fn "round" [cst (VD 25 1)]) = "3".
Proof. check. Qed.

(** [float8] to [numeric]: 15 significant digits *)
Example pg_to_numeric : text PostgreSQL (fn "cast_numeric" [fn "+" [d01; d02]]) = "0.3".
Proof. check. Qed.

(** NaN is equal to itself and greater than every number in PostgreSQL *)
Definition holds (d : vsem) (c : scond) : bool :=
  Nat.eqb (List.length (run d (select_where [as_ (int 1) c0] [] c))) 1.

Example pg_nan_eq : holds PostgreSQL (pred "=" [fn "cast_float8" [str "NaN"]; fn "cast_float8" [str "NaN"]]) = true.
Proof. check. Qed.

Example pg_nan_greatest : holds PostgreSQL (pred ">" [fn "cast_float8" [str "NaN"]; fn "cast_float8" [str "Infinity"]]) = true.
Proof. check. Qed.

(** sum of binary32 values as doubles, one rounding per addition *)
Definition floats := values_ [c0] [[cst (VFl true 4523 (-2))]; [cst (VFl true 4523 (-2))]; [cst (VFl true 5711 (-2))]].

Example my_sum_float32 :
  map (fun t => show_value (dot (TD MySQL) t (out_attr 0)))
      (run MySQL (select_where [as_ (agg "sum" (col c0)) c0] [from_as floats [(c0, c0)]] c_true)) = ["147.56999969482422"].
Proof. check. Qed.
