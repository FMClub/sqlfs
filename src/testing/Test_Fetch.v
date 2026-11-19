(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Tests of FETCH FIRST ... WITH TIES and PERCENT.                               *)
(**                                                                                 *)
(************************************************************************************)

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

Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).

Definition shown (d : vsem) (q : squery) : list string :=
  map (fun t => show_value (dot (TD d) t (out_attr 0))) (run d q).

Definition nums := values_ [c0] [[int 3]; [int 1]; [int 2]; [int 2]; [int 2]; [int 5]].

Definition fetch off ties pct n :=
  fetch_first nums [o_by (col c0) Asc] off ties pct n.

Example rows_only : shown PostgreSQL (fetch None false false 2%N) = ["1"; "2"].
Proof. check. Qed.

(** the three rows equal to the last one are returned *)
Example with_ties : shown PostgreSQL (fetch None true false 2%N) = ["1"; "2"; "2"; "2"].
Proof. check. Qed.

Example with_ties_offset : shown PostgreSQL (fetch (Some 1%N) true false 1%N) = ["2"; "2"; "2"].
Proof. check. Qed.

(** 50 percent of 6 rows: 3 rows; 40 percent: ceil(2.4) = 3 rows *)
Example percent : shown OceanBaseOracle (fetch None false true 50%N) = ["1"; "2"; "2"].
Proof. check. Qed.

Example percent_round_up : shown OceanBaseOracle (fetch None false true 40%N) = ["1"; "2"; "2"].
Proof. check. Qed.

Example percent_ties : shown OceanBaseOracle (fetch None true true 40%N) = ["1"; "2"; "2"; "2"].
Proof. check. Qed.

Definition acceptance (q : squery) := 
  map (fun d => accepted_by (dialect_of d) (to_dialect d q)) 
      [PostgreSQL; MySQL; SQLite; OceanBaseMySQL; OceanBaseOracle].

Example accepted_ties : acceptance (fetch None true false 2%N) = [true; false; false; false; true].
Proof. check. Qed.

Example accepted_percent : acceptance (fetch None false true 2%N) = [false; false; false; false; true].
Proof. check. Qed.

(** * Aggregates with a separator and an ORDER BY *)

Definition words := values_ [c0] [[int 3]; [int 1]; [int 2]].

Definition ordered_concat f sep dir :=
  select_where [as_ (agg_x f (col c0) sep [o_by (col c0) dir]) (Attr_Z "c1")] [from_as words [(c0, c0)]] c_true.

(** [group_concat (c0 ORDER BY c0 DESC SEPARATOR '-')] *)
Example group_concat_ordered :
  shown MySQL (select_where [as_ (agg_x "group_concat_sep" (col c0) (Some (str "-")) [o_by (col c0) Desc]) c0] [from_as words [(c0, c0)]] c_true) = ["3-2-1"].
Proof. check. Qed.

(** [string_agg (c0, ', ' ORDER BY c0)] *)
Example string_agg_ordered :
  shown PostgreSQL (select_where [as_ (agg_x "string_agg_sep" (col c0) (Some (str ", ")) [o_by (col c0) Asc]) c0] [from_as words [(c0, c0)]] c_true) = ["1, 2, 3"].
Proof. check. Qed.

Example listagg_ordered :
  shown OceanBaseOracle (select_where [as_ (agg_x "listagg" (col c0) None [o_by (col c0) Asc]) c0] [from_as words [(c0, c0)]] c_true) = ["123"].
Proof. check. Qed.

(** * DISTINCT ON *)

Notation c1' := (Attr_Z "c1").

Definition kv := values_ [c0; c1'] [[int 1; int 5]; [int 1; int 3]; [int 2; int 7]].

Example distinct_on_first :
  map (fun t => map (fun i => show_value (dot (TD PostgreSQL) t (out_attr i))) (seq 0 2))
      (run PostgreSQL (select_where [as_ (col c0) c0; as_ (col c1') c1'] [from_query (distinct_on kv [c0; c1'] [col c0] [o_by (col c1') Asc] (Attr_Z "rn"))] c_true))
  = [["1"; "3"]; ["2"; "7"]].
Proof. check. Qed.
