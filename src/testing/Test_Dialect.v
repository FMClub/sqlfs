(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Tests of the dialect framework of SqlFull: the same query gets different      *)
(**   results from different dialects.                                              *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String ZArith NArith.

Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.

Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax.

Import Tuple.
Import ListNotations.
Open Scope string_scope.

Ltac check := vm_compute; reflexivity.

Notation nm := (Attr_string "nm").
Notation n := (Attr_Z "n").
Notation k := (Attr_Z "k").
Notation c := (Attr_Z "c").
Notation nm2 := (Attr_string "nm2").
Notation n2 := (Attr_Z "n2").

(** p (nm, n):  Bob 1,  bob 2,  Alice 3,  NULL 4 
    q (nm, n):  BOB 1,  Alice 5 *)
Definition db : db_state :=
  mk_insert 
    (mk_insert 
       (create_table (create_table init_db (Rel "p") [nm; n]) (Rel "q") [nm; n])
       (Rel "p") [nm; n]
       [ [VS "Bob"; VZ 1]; [VS "bob"; VZ 2]; [VS "Alice"; VZ 3]; [NullS; VZ 4] ])
    (Rel "q") [nm; n] [ [VS "BOB"; VZ 1]; [VS "Alice"; VZ 5] ].

(** A dialect which differs from TNull_PostgreSQL by its case insensitive collation, by the 
    NULLs being the smallest values, and by the lack of some constructs. *)
Definition fold_case v := 
  match v with 
  | NullValues.Value_string (Some s) => NullValues.Value_string (Some (NullValues.string_map NullValues.lower_ascii s))
  | _ => v 
  end.

(** the constructs of [CI] *)
Definition CI_supports (f : feature) : bool :=
  match f with
  | F_Full_Join | F_Frame_Groups | F_Filter_Agg | F_Nulls_Order => false
  | _ => true
  end.

Definition CI : dialect TNull :=
  mk_dialect TNull
             NullValues.is_null
             (NullValues.Value_Z None)
             NullValues.bool3_of_value
             NullValues.value_of_bool3
             (fun a b => NullValues.sql_eq3 (fold_case a) (fold_case b))
             (fun a b => NullValues.sql_order (fold_case a) (fold_case b))
             (fun z => NullValues.Value_Z (Some z))
             NullValues.rat_of_value
             NullValues.value_of_rat
             fold_case
             true
             (fun _ _ => true) (fun _ => true) (fun _ => true)
             NullValues.is_err NullValues.Value_Err (Attr_string "#error")
             NullValues.is_lazy_symbol (fun _ _ => false) false (fun v => v) (fun _ => false)
             (fun _ => 0%nat) (fun _ _ l => l) (fun l => l) (fun _ => None)
             NullValues.interp_symbol NullValues.interp_predicate NullValues.interp_aggregate.

Definition run (d : dialect TNull) q := 
  List.map (show_tuple TNull) 
           (eval_query_list ORN d (_basesort _ db) (_instance _ db) q).

Definition rows (d : dialect TNull) q atts expected := 
  let res := eval_query_list ORN d (_basesort _ db) (_instance _ db) q in
  rows_permb (List.map (row_of atts) res) expected.

Definition rows_ordered (d : dialect TNull) q atts expected := 
  let res := eval_query_list ORN d (_basesort _ db) (_instance _ db) q in
  rows_eqb (List.map (row_of atts) res) expected.

Definition names := select_where [as_ (col nm) nm] [from_table "p"] c_true.

(** * DISTINCT, GROUP BY: the keys of the values *)

Definition distinct_names := select_distinct [as_ (col nm) nm] [from_table "p"] c_true.

Example distinct_pg : 
  rows TNull_PostgreSQL distinct_names [nm] [ [VS "Bob"]; [VS "bob"]; [VS "Alice"]; [NullS] ] = true.
Proof. check. Qed.

(** The first occurrence is kept. *)
Example distinct_ci : 
  rows CI distinct_names [nm] [ [VS "Bob"]; [VS "Alice"]; [NullS] ] = true.
Proof. check. Qed.

Definition group_names := 
  select_group [as_ (col nm) nm; as_ count_star c; as_ (agg "sum" (col n)) k] 
               [from_table "p"] c_true [col nm] c_true.

Example group_pg :
  rows TNull_PostgreSQL group_names [nm; c; k] 
    [ [VS "Bob"; VZ 1; VZ 1]; [VS "bob"; VZ 1; VZ 2]; [VS "Alice"; VZ 1; VZ 3]; [NullS; VZ 1; VZ 4] ] 
  = true.
Proof. check. Qed.

Example group_ci :
  rows CI group_names [nm; c; k] 
    [ [VS "Bob"; VZ 2; VZ 3]; [VS "Alice"; VZ 1; VZ 3]; [NullS; VZ 1; VZ 4] ] = true.
Proof. check. Qed.

(** [count(DISTINCT nm)]: the NULL is not counted. *)
Example count_distinct_pg :
  rows TNull_PostgreSQL (select_where [as_ (agg_distinct "count" (col nm)) c] [from_table "p"] c_true)
       [c] [ [VZ 3] ] = true.
Proof. check. Qed.

Example count_distinct_ci :
  rows CI (select_where [as_ (agg_distinct "count" (col nm)) c] [from_table "p"] c_true)
       [c] [ [VZ 2] ] = true.
Proof. check. Qed.

(** * Set operations *)

Definition qnames := select_where [as_ (col nm) nm] [from_table "q"] c_true.

Example union_pg :
  rows TNull_PostgreSQL (set_op_ Union Set_Distinct names qnames) [nm] 
    [ [VS "Bob"]; [VS "bob"]; [VS "Alice"]; [NullS]; [VS "BOB"] ] = true.
Proof. check. Qed.

Example union_ci :
  rows CI (set_op_ Union Set_Distinct names qnames) [nm] 
    [ [VS "Bob"]; [VS "Alice"]; [NullS] ] = true.
Proof. check. Qed.

Example intersect_pg :
  rows TNull_PostgreSQL (set_op_ Inter Set_Distinct names qnames) [nm] [ [VS "Alice"] ] = true.
Proof. check. Qed.

Example intersect_ci :
  rows CI (set_op_ Inter Set_Distinct names qnames) [nm] [ [VS "Bob"]; [VS "Alice"] ] = true.
Proof. check. Qed.

(** [INTERSECT ALL] and [EXCEPT ALL]: the minimum and the difference of the multiplicities. *)
Definition xs := values_ [n] [ [int 1]; [int 1]; [int 1]; [int 2]; [int 3] ].
Definition ys := values_ [n] [ [int 1]; [int 1]; [int 2]; [int 2]; [int 4] ].

Example intersect_all :
  rows TNull_PostgreSQL (set_op_ Inter Set_All xs ys) [n] [ [VZ 1]; [VZ 1]; [VZ 2] ] = true.
Proof. check. Qed.

Example except_all :
  rows TNull_PostgreSQL (set_op_ Diff Set_All xs ys) [n] [ [VZ 1]; [VZ 3] ] = true.
Proof. check. Qed.

Example except_all_2 :
  rows TNull_PostgreSQL (set_op_ Diff Set_All ys xs) [n] [ [VZ 2]; [VZ 4] ] = true.
Proof. check. Qed.

(** * ORDER BY: the position of the NULLs *)

Definition by_name d := order_by names [o_by (col nm) d].

Example nulls_last_pg : 
  rows_ordered TNull_PostgreSQL (by_name Asc) [nm] 
    [ [VS "Alice"]; [VS "Bob"]; [VS "bob"]; [NullS] ] = true.
Proof. check. Qed.

Example nulls_first_pg_desc : 
  rows_ordered TNull_PostgreSQL (by_name Desc) [nm] 
    [ [NullS]; [VS "bob"]; [VS "Bob"]; [VS "Alice"] ] = true.
Proof. check. Qed.

(** The NULL is the smallest value; "Bob" and "bob" are equal for the order, and keep
    their relative order. *)
Example nulls_first_ci : 
  rows_ordered CI (by_name Asc) [nm] [ [NullS]; [VS "Alice"]; [VS "Bob"]; [VS "bob"] ] = true.
Proof. check. Qed.

Example nulls_last_ci_desc : 
  rows_ordered CI (by_name Desc) [nm] [ [VS "Bob"]; [VS "bob"]; [VS "Alice"]; [NullS] ] = true.
Proof. check. Qed.

(** An explicit NULLS clause overrides the default of the dialect. *)
Example nulls_explicit : 
  rows_ordered TNull_PostgreSQL 
    (order_by names [o_by_nulls (col nm) Asc Nulls_First]) [nm] 
    [ [NullS]; [VS "Alice"]; [VS "Bob"]; [VS "bob"] ] = true.
Proof. check. Qed.

(** * Joins and comparisons use the order of the dialect *)

Example join_pg :
  rows TNull_PostgreSQL 
    (select_where [as_ (col nm) nm; as_ (col n2) n2]
       [join J_Inner (from_table "p") 
             (from_as (table "q") [(nm, nm2); (n, n2)]) (pred "=" [col nm; col nm2])] c_true)
    [nm; n2] [ [VS "Alice"; VZ 5] ] = true.
Proof. check. Qed.

(** * Windows: the peers are given by the order of the dialect *)

Definition rank_names :=
  select_where [as_ (col nm) nm; as_ (col k) k]
    [from_query (window names [w_as w_rank [] [o_by (col nm) Asc] k])] c_true.

Example rank_pg :
  rows TNull_PostgreSQL rank_names [nm; k] 
    [ [VS "Alice"; VZ 1]; [VS "Bob"; VZ 2]; [VS "bob"; VZ 3]; [NullS; VZ 4] ] = true.
Proof. check. Qed.

Example rank_ci :
  rows CI rank_names [nm; k] 
    [ [NullS; VZ 1]; [VS "Alice"; VZ 2]; [VS "Bob"; VZ 3]; [VS "bob"; VZ 3] ] = true.
Proof. check. Qed.

(** * Which dialect accepts which query *)

Definition full_join_query := 
  select_star_where [join J_Full (from_table "p") (from_table "q") c_true] c_true.
Definition lateral_query := 
  select_star_where [join_lateral J_Inner (from_table "p") (from_table "q") c_true] c_true.
Definition nulls_query := order_by names [o_by_nulls (col nm) Asc Nulls_Last].
Definition groups_frame_query := 
  window names [w_as (w_agg "count" (col nm) (Frame_Groups Unbounded_Preceding Current_Row)) 
                     [] [o_by (col nm) Asc] k].

Example features_1 : 
  squery_features full_join_query = [F_Full_Join]. Proof. check. Qed.
Example features_2 : 
  squery_features lateral_query = [F_Lateral]. Proof. check. Qed.
Example features_3 : 
  squery_features (set_op_ Diff Set_All xs ys) = [F_Except; F_Except_All]. Proof. check. Qed.
Example features_4 : 
  squery_features groups_frame_query = [F_Window; F_Frame_Groups]. Proof. check. Qed.

Example accepted_pg : 
  forallb (fun q => accepted_by TNull_PostgreSQL (fun _ => true) q) 
          [full_join_query; lateral_query; nulls_query; groups_frame_query] = true.
Proof. check. Qed.

Example rejected_ci : 
  map (fun q => accepted_by CI CI_supports q) [full_join_query; lateral_query; nulls_query; groups_frame_query]
  = [false; true; false; false].
Proof. check. Qed.
