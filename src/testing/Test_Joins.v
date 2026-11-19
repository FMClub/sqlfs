(** * Joins (TODO 3.2): [ON] and [WHERE] of outer joins, [CROSS APPLY], [OUTER APPLY] *)
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
Notation b := (Attr_Z "b").
Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).
Definition rows (d : vsem) (q : squery) (n : nat) : list (list string) :=
  map (fun t => map (fun i => show_value (dot (TD d) t (out_attr i))) (seq 0 n)) (run d q).
Definition accepts (d : vsem) (q : squery) : bool := accepted_by (dialect_of d) (to_dialect d q).

Definition l := from_as (values_ [c0] [[int 1]; [int 2]]) [(c0, a)].
Definition r := from_as (values_ [c0] [[int 1]; [int 3]]) [(c0, b)].
Definition out := [as_ (col a) c0; as_ (col b) c1].

(** [l LEFT JOIN r ON a = b AND b = 1] keeps both rows of [l] ... *)
Example on_keeps :
  rows PostgreSQL (select_where out [join J_Left l r (c_and (pred "=" [col a; col b]) (pred "=" [col b; int 1]))] c_true) 2
  = [["1"; "1"]; ["2"; "NULL"]].
Proof. check. Qed.
(** ... while [WHERE b = 1] removes the padded row: a condition cannot be moved from [WHERE] to [ON] of an
    outer join (it can for an inner join: [inner_join_where] in [SqlFullFacts.v]) *)
Example where_filters :
  rows PostgreSQL (select_where out [join J_Left l r (pred "=" [col a; col b])] (pred "=" [col b; int 1])) 2
  = [["1"; "1"]].
Proof. check. Qed.
(** inner join: both places give the same rows *)
Example inner_same :
  rows PostgreSQL (select_where out [join J_Inner l r (c_and (pred "=" [col a; col b]) (pred "=" [col b; int 1]))] c_true) 2
  = rows PostgreSQL (select_where out [join J_Inner l r (pred "=" [col a; col b])] (pred "=" [col b; int 1])) 2.
Proof. check. Qed.
(** a full join with a non-equality condition *)
Example full_non_equi :
  rows PostgreSQL (select_where out [join J_Full l r (pred "<" [col a; col b])] c_true) 2
  = [["1"; "3"]; ["2"; "3"]; ["NULL"; "1"]].
Proof. check. Qed.

(** [CROSS APPLY] and [OUTER APPLY] (Oracle mode): the right operand reads the left row *)
Definition dep := from_as (select_where [as_ (fn "+" [col a; int 10]) c0] [] (pred "<" [col a; int 2])) [(c0, b)].
Example cross_apply_rows : rows OceanBaseOracle (select_where out [cross_apply l dep] c_true) 2 = [["1"; "11"]].
Proof. check. Qed.
Example outer_apply_rows : rows OceanBaseOracle (select_where out [outer_apply l dep] c_true) 2 = [["1"; "11"]; ["2"; "NULL"]].
Proof. check. Qed.
(** SQLite has no lateral join *)
Example lite_no_lateral : accepts SQLite (select_where out [cross_apply l dep] c_true) = false.
Proof. check. Qed.
