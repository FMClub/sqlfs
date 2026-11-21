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
  accepted_by (dialect_of d) (vs_supports d) (to_dialect d (select_where [as_ e c0] [] c_true)).

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

(** Static errors which the dialects share or differ on (the cases of the suites which expect an error; TODO 8.25):
    an aggregate in [GROUP BY] is rejected by every dialect; a [SELECT DISTINCT] ordered by an expression which
    is not selected is rejected by PostgreSQL, by Oracle mode and by [ONLY_FULL_GROUP_BY] (MySQL, TiDB), and
    accepted by SQLite, MariaDB and OceanBase's MySQL mode *)
Require Import TiDB.

Definition accepts_q (d : vsem) (q : squery) : bool :=
  accepted_by (dialect_of d) (vs_supports d) (to_dialect d q).
Notation v1 := (Attr_Z "v1").
Notation v2 := (Attr_Z "v2").
Definition tt := from_as (values_ [c0; Attr_Z "c1"] [[int 1; int 2]]) [(c0, v1); (Attr_Z "c1", v2)].
Definition group_by_agg := select_full Set_All (s_list [as_ (int 1) c0]) [tt] c_true (g_by [agg "sum" (col v1)]) c_true.
Definition distinct_order (key : sexpr) :=
  order_by (select_full Set_Distinct (s_list [as_ (col v1) c0]) [tt] c_true g_fine c_true) [o_by key Asc].

Example group_agg_rejected :
  map (fun d => accepts_q d group_by_agg) [PostgreSQL; MySQL; SQLite; MariaDB; OceanBaseMySQL; OceanBaseOracle; TiDB] =
  [false; false; false; false; false; false; false].
Proof. check. Qed.
Example distinct_order_not_selected :
  map (fun d => accepts_q d (distinct_order (col v2))) [PostgreSQL; MySQL; TiDB; OceanBaseOracle; SQLite; MariaDB; OceanBaseMySQL] =
  [false; false; false; false; true; true; true].
Proof. check. Qed.
(** the selected expression itself, or its output name, is accepted *)
Example distinct_order_selected :
  accepts_q PostgreSQL (distinct_order (col v1)) = true /\ accepts_q PostgreSQL (distinct_order (col c0)) = true.
Proof. split; check. Qed.
