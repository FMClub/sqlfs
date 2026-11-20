(** * Well-formedness of queries (TODO 6.2) *)
Require Import List String ZArith.
Require Import Bool3 FlatData ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.
Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax SpecRunner SqlWellFormed.
Import ListNotations.
Open Scope string_scope.
Ltac check := vm_compute; reflexivity.
Notation c0 := (Attr_Z "c0").
Notation c1 := (Attr_Z "c1").
Notation a := (Attr_Z "a").
Definition wf q := wf_query TNull relname ORN (_basesort _ init_db) nil q.
Definition t := values_ [a] [[int 1]; [int 2]].

(** a closed query *)
Example wf_ok : wf (select_where [as_ (col a) c0] [from_query t] (pred "=" [col a; int 1])) = true.
Proof. check. Qed.
(** a column which no FROM clause binds *)
Example wf_unbound : wf (select_where [as_ (col (Attr_Z "b")) c0] [from_query t] c_true) = false.
Proof. check. Qed.
(** an aggregate of the block in WHERE *)
Example wf_agg_where : wf (select_where [as_ (col a) c0] [from_query t] (pred ">" [agg "sum" (col a); int 1])) = false.
Proof. check. Qed.
(** a set operation whose operands do not have the same columns *)
Example wf_union_arity :
  wf (set_op_ Union Set_All (select_where [as_ (col a) c0] [from_query t] c_true)
                            (select_where [as_ (col a) c0; as_ (col a) c1] [from_query t] c_true)) = false.
Proof. check. Qed.
(** a correlated subquery: its free column is bound by the enclosing block *)
Example wf_correlated :
  wf (select_where [as_ (col a) c0] [from_query t]
        (c_exists (select_where [as_ (int 1) c1] [from_as t [(a, Attr_Z "b")]] (pred "=" [col (Attr_Z "b"); col a])))) = true.
Proof. check. Qed.
