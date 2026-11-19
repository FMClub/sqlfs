(** * Comparison and conditional functions (TODO 2.3)

    The functions of the C library ([sqrt], [exp], [ln], [sin], ...) are correctly rounded; the
    [numeric] versions of PostgreSQL have the scale of [numeric.c]. The expected texts are the ones of
    the engines. *)
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

Definition dbl (n : Z) := cst (VFl false n 0).
Definition s (x : string) := str x.
Definition holds (d : vsem) (c : scond) : bool :=
  match run d (select_where [as_ (int 1) c0] [] c) with nil => false | _ => true end.

(** [IN] with NULL: [1 IN (2, NULL)] is UNKNOWN, [1 NOT IN (2, NULL)] too, [1 IN (1, NULL)] is TRUE *)
Example in_null_pg : holds PostgreSQL (pred "in" [int 1; int 2; cst NullZ]) = false.
Proof. check. Qed.
Example not_in_null_pg : holds PostgreSQL (pred "not in" [int 1; int 2; cst NullZ]) = false.
Proof. check. Qed.
Example in_hit_my : holds MySQL (pred "in" [int 1; int 1; cst NullZ]) = true.
Proof. check. Qed.
Example not_in_null_lite : holds SQLite (pred "not in" [int 1; int 2; cst NullZ]) = false.
Proof. check. Qed.

(** [BETWEEN SYMMETRIC] (PostgreSQL) *)
Example between_sym : holds PostgreSQL (pred "between symmetric" [int 5; int 10; int 1]) = true.
Proof. check. Qed.
Example between_asym : holds PostgreSQL (pred "between" [int 5; int 10; int 1]) = false.
Proof. check. Qed.

(** [IS DISTINCT FROM], [<=>] *)
Example distinct_pg : holds PostgreSQL (pred "is distinct from" [int 1; cst NullZ]) = true.
Proof. check. Qed.
Example null_safe_my : holds MySQL (pred "<=>" [cst NullZ; cst NullZ]) = true.
Proof. check. Qed.

(** [GREATEST] / [LEAST]: PostgreSQL ignores the NULLs, MySQL and Oracle give NULL *)
Example greatest_pg : text PostgreSQL (fn "greatest" [int 1; cst NullZ; int 3]) = "3".
Proof. check. Qed.
Example greatest_my : text MySQL (fn "greatest" [int 1; cst NullZ; int 3]) = "NULL".
Proof. check. Qed.
Example greatest_ora : text OceanBaseOracle (fn "greatest" [int 1; cst NullZ; int 3]) = "NULL".
Proof. check. Qed.

(** SQLite scalar [max] / [min] *)
Example lite_max : text SQLite (fn "max_scalar" [int 1; int 5; int 3]) = "5".
Proof. check. Qed.
Example lite_max_null : text SQLite (fn "max_scalar" [int 1; cst NullZ]) = "NULL".
Proof. check. Qed.
Example lite_min_mixed : text SQLite (fn "min_scalar" [s "a"; int 5]) = "5".
Proof. check. Qed.

(** Oracle [DECODE]: two NULLs are equal *)
Example decode_hit : text OceanBaseOracle (fn "decode" [int 2; int 1; s "one"; int 2; s "two"; s "other"]) = "two".
Proof. check. Qed.
Example decode_null : text OceanBaseOracle (fn "decode" [cst NullZ; cst NullZ; s "null"; s "other"]) = "null".
Proof. check. Qed.
Example decode_default : text OceanBaseOracle (fn "decode" [int 9; int 1; s "one"]) = "NULL".
Proof. check. Qed.
Example nvl2_ora : text OceanBaseOracle (fn "nvl2" [s ""; s "a"; s "b"]) = "b".
Proof. check. Qed.

(** MySQL [ISNULL], [INTERVAL], [IF], [IFNULL], [NULLIF] *)
Example isnull_my : text MySQL (fn "isnull" [cst NullZ]) = "1".
Proof. check. Qed.
Example interval_my : text MySQL (fn "interval_index" [int 23; int 1; int 15; int 17; int 30; int 44; int 200]) = "3".
Proof. check. Qed.
Example interval_my_null : text MySQL (fn "interval_index" [cst NullZ; int 1]) = "-1".
Proof. check. Qed.
Example nullif_my : text MySQL (fn "nullif" [int 1; int 1]) = "NULL".
Proof. check. Qed.
Example ifnull_lite : text SQLite (fn "ifnull" [cst NullZ; int 2]) = "2".
Proof. check. Qed.
Example iif_lite : text SQLite (fn "iif" [e_cond (pred "<" [int 1; int 2]); s "yes"; s "no"]) = "yes".
Proof. check. Qed.

(** PostgreSQL [num_nulls], [num_nonnulls]; SQLite [likely] *)
Example num_nulls : text PostgreSQL (fn "num_nulls" [int 1; cst NullZ; cst NullZ]) = "2".
Proof. check. Qed.
Example num_nonnulls : text PostgreSQL (fn "num_nonnulls" [int 1; cst NullZ; cst NullZ]) = "1".
Proof. check. Qed.
Example likely_lite : text SQLite (fn "likely" [int 7]) = "7".
Proof. check. Qed.
