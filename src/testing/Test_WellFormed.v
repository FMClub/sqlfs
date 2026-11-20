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

(** * Coverage of GROUP BY with the functional dependencies of keys: the table [t] has the key [id] *)
Definition keys (r : relname) : list attribute :=
  match r with Rel "t" => [Attr_Z "id"] | _ => nil end.
Definition tk := from_as (table "t") [(Attr_Z "id", Attr_Z "t.id"); (Attr_Z "v", Attr_Z "t.v"); (Attr_Z "w", Attr_Z "t.w")].
Definition by_key :=
  select_full Set_All (s_list [as_ (col (Attr_Z "t.id")) c0; as_ (col (Attr_Z "t.v")) c1]) [tk] c_true
              (g_by [col (Attr_Z "t.id")]) c_true.
(** [t.v] is determined by the key [t.id], which is grouped *)
Example covered_by_key : group_covered TNull relname keys by_key = true.
Proof. check. Qed.
(** without the key, [t.v] is a bare column *)
Example bare_without_key : group_covered TNull relname (fun _ => nil) by_key = false.
Proof. check. Qed.
(** grouping by a column which is not the key determines nothing *)
Example bare_other_group :
  group_covered TNull relname keys
    (select_full Set_All (s_list [as_ (col (Attr_Z "t.v")) c0; as_ count_star c1]) [tk] c_true
                 (g_by [col (Attr_Z "t.w")]) c_true) = false.
Proof. check. Qed.
(** an aggregate without GROUP BY reads no bare column *)
Example covered_aggregate :
  group_covered TNull relname keys
    (select_full Set_All (s_list [as_ count_star c0]) [tk] c_true g_fine c_true) = true.
Proof. check. Qed.

(** * Ambiguity: two tables of the FROM clause have the column [a] *)
Example wf_ambiguous :
  wf (select_where [as_ (col a) c0] [from_query t; from_query t] c_true) = false.
Proof. check. Qed.
(** inside a join too *)
Example wf_ambiguous_join :
  wf (select_where [as_ (col a) c0] [join J_Inner (from_query t) (from_query t) c_true] c_true) = false.
Proof. check. Qed.
(** the columns renamed apart are not ambiguous *)
Example wf_renamed :
  wf (select_where [as_ (col (Attr_Z "x.a")) c0] [from_as t [(a, Attr_Z "x.a")]; from_as t [(a, Attr_Z "y.a")]]
        c_true) = true.
Proof. check. Qed.
