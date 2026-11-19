(** * Arity checking and unknown functions (TODO 2.10)

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
Require Import MariaDB.

Definition accepts (d : vsem) (e : sexpr) : bool :=
  accepted_by (dialect_of d) (to_dialect d (select_where [as_ e c0] [] c_true)).

(** [LPAD] takes three arguments in MySQL, two or three in MariaDB and PostgreSQL *)
Example lpad_my : accepts MySQL (fn "lpad" [str "a"; int 3]) = false.
Proof. check. Qed.
Example lpad_maria : accepts MariaDB (fn "lpad" [str "a"; int 3]) = true.
Proof. check. Qed.
Example lpad_pg : accepts PostgreSQL (fn "lpad" [str "a"; int 3]) = true.
Proof. check. Qed.
Example lpad_my_eval : fails MySQL (fn "lpad" [str "a"; int 3]) = true.
Proof. check. Qed.
(** an unknown function is rejected, and its evaluation is an error (not NULL) *)
Example unknown_acc : accepts PostgreSQL (fn "no_such_function" [int 1]) = false.
Proof. check. Qed.
Example unknown_eval : fails PostgreSQL (fn "no_such_function" [int 1]) = true.
Proof. check. Qed.
(** [COALESCE] needs two arguments in SQLite, one in PostgreSQL *)
Example coalesce_lite : accepts SQLite (fn "coalesce" [int 1]) = false.
Proof. check. Qed.
Example coalesce_pg : accepts PostgreSQL (fn "coalesce" [int 1]) = true.
Proof. check. Qed.
(** [GREATEST] needs two arguments in MySQL *)
Example greatest_my : accepts MySQL (fn "greatest" [int 1]) = false.
Proof. check. Qed.
Example round_ok : accepts MySQL (fn "round" [int 1; int 2]) = true.
Proof. check. Qed.
Example round_too_many : accepts MySQL (fn "round" [int 1; int 2; int 3]) = false.
Proof. check. Qed.
