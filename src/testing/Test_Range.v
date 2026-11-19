(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Tests of RANGE window frames with offsets.                                    *)
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
Notation c1 := (Attr_Z "c1").

Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).

Definition result_is (d : vsem) (q : squery) (n : nat) (expected : list (list string)) : bool :=
  match_unordered 
    (map (fun t => map (fun i => dot (TD d) t (out_attr i)) (seq 0 n)) (run d q)) expected.

Definition nums := values_ [c0] [[int 1]; [int 2]; [int 2]; [int 4]; [int 7]; [cst (NullValues.Value_Z None)]].

Definition sums dir lo hi :=
  window nums [w_as (w_agg "sum" (col c0) (Frame_Range lo hi)) [] [o_by (col c0) dir] c1].

(** [sum(c0) OVER (ORDER BY c0 RANGE BETWEEN 2 PRECEDING AND 1 FOLLOWING)] *)
Example range_asc : 
  result_is PostgreSQL (sums Asc (Preceding 2) (Following 1)) 2
    [["1"; "5"]; ["2"; "5"]; ["2"; "5"]; ["4"; "8"]; ["7"; "7"]; ["NULL"; "NULL"]] = true.
Proof. check. Qed.

(** the frame of a descending order is mirrored: rows with a key in [v - 1, v + 2] *)
Example range_desc : 
  result_is PostgreSQL (sums Desc (Preceding 2) (Following 1)) 2
    [["1"; "5"]; ["2"; "9"]; ["2"; "9"]; ["4"; "4"]; ["7"; "7"]; ["NULL"; "NULL"]] = true.
Proof. check. Qed.

(** [RANGE BETWEEN CURRENT ROW AND 2 FOLLOWING] includes the peers *)
Example range_current : 
  result_is PostgreSQL (sums Asc Current_Row (Following 2)) 2
    [["1"; "5"]; ["2"; "8"]; ["2"; "8"]; ["4"; "4"]; ["7"; "7"]; ["NULL"; "NULL"]] = true.
Proof. check. Qed.

Example range_unbounded : 
  result_is MySQL (sums Asc Unbounded_Preceding (Following 1)) 2
    [["1"; "5"]; ["2"; "5"]; ["2"; "5"]; ["4"; "9"]; ["7"; "16"]; ["NULL"; "NULL"]] = true.
Proof. check. Qed.
