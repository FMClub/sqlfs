(** * Scalar subqueries, [EXISTS], [ANY] / [ALL] (TODO 3.8) *)
Require Import List String ZArith NArith.
Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.
Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax
        Dialects PostgreSQL MySQL SQLite OceanBase SpecRunner.
Import Tuple.
Import ListNotations.
Open Scope string_scope.
Ltac check := vm_compute; reflexivity.
Notation c0 := (Attr_Z "c0").
Notation c1 := (Attr_Z "c1").
Notation a := (Attr_Z "a").
Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).
Definition col0 (d : vsem) (q : squery) : list string :=
  map (fun t => show_value (dot (TD d) t (out_attr 0))) (run d q).
Definition fails (d : vsem) (q : squery) : bool :=
  match eval_query_result ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q) with
  | QR_Error _ => true | _ => false end.
Definition truth (d : vsem) (c : scond) : string :=
  match run d (select_where [as_ (int 1) c0] [] c), run d (select_where [as_ (int 1) c0] [] (c_not c)) with
  | _ :: _, _ => "t" | nil, _ :: _ => "f" | nil, nil => "u" end.

Definition empty := select_where [as_ (int 1) c0] [] (c_not c_true).
Definition two := values_ [c0] [[int 1]; [int 2]].
Definition with_null := values_ [c0] [[int 1]; [cst NullZ]].

(** a scalar subquery without row is NULL; with two rows it is an error (SQLite takes the first row) *)
Example sub_empty : col0 PostgreSQL (select_where [as_ (e_sub empty) c0] [] c_true) = ["NULL"].
Proof. check. Qed.
Example sub_two_pg : fails PostgreSQL (select_where [as_ (e_sub two) c0] [] c_true) = true.
Proof. check. Qed.
Example sub_two_my : fails MySQL (select_where [as_ (e_sub two) c0] [] c_true) = true.
Proof. check. Qed.
Example sub_two_lite : col0 SQLite (select_where [as_ (e_sub two) c0] [] c_true) = ["1"].
Proof. check. Qed.
(** [ALL] of an empty set is true, [ANY] of an empty set is false *)
Example all_empty : truth PostgreSQL (c_all ">" [int 5] empty [c0]) = "t".
Proof. check. Qed.
Example any_empty : truth PostgreSQL (c_any ">" [int 5] empty [c0]) = "f".
Proof. check. Qed.
(** with a NULL: [5 > ALL (1, NULL)] is UNKNOWN, [5 > ANY (1, NULL)] is true, [0 > ANY (1, NULL)] UNKNOWN *)
Example all_null : truth MySQL (c_all ">" [int 5] with_null [c0]) = "u".
Proof. check. Qed.
Example any_null_true : truth MySQL (c_any ">" [int 5] with_null [c0]) = "t".
Proof. check. Qed.
Example any_null_unknown : truth MySQL (c_any ">" [int 0] with_null [c0]) = "u".
Proof. check. Qed.
(** [IN] a [UNION] *)
Example in_union : truth PostgreSQL (c_in [int 2] (set_op_ Union Set_All empty two) [c0]) = "t".
Proof. check. Qed.
(** [NOT EXISTS] of an empty query *)
Example not_exists : truth SQLite (c_not (c_exists empty)) = "t".
Proof. check. Qed.
(** a correlated subquery in [HAVING]: the groups whose count is the number of rows of a correlated
    query (the outer column is read in the subquery) *)
Definition t := from_as two [(c0, a)].
Example correlated_having :
  col0 PostgreSQL (select_full Set_All (s_list [as_ (col a) c0]) [t] c_true (g_by [col a])
                     (pred "=" [agg "count" (col a);
                                e_sub (select_where [as_ (agg "count" (int 1)) c1] [] (pred "<" [col a; int 2]))]))
  = ["1"].
Proof. check. Qed.
