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

(** * PERCENT_RANK and CUME_DIST *)

Definition five := values_ [c0] [[int 1]; [int 2]; [int 2]; [int 3]; [int 5]].
Definition ranks f := window five [w_as f [] [o_by (col c0) Asc] c1].

Example percent_rank_values : 
  result_is PostgreSQL (ranks w_percent_rank) 2
    [["1"; "0"]; ["2"; "0.25"]; ["2"; "0.25"]; ["3"; "0.75"]; ["5"; "1"]] = true.
Proof. check. Qed.

Example cume_dist_values : 
  result_is MySQL (ranks w_cume_dist) 2
    [["1"; "0.2"]; ["2"; "0.6"]; ["2"; "0.6"]; ["3"; "0.8"]; ["5"; "1"]] = true.
Proof. check. Qed.

Require Import MariaDB.

(** the type of the result (TODO 8.31): a double, of 10 decimals in MariaDB ([win_percent_cume.result]); an exact
    number in Oracle mode *)
Definition is_double (d : vsem) (q : squery) : bool :=
  forallb (fun t => match dot (TD d) t (out_attr 1) with NullValues.Value_F _ => true | _ => false end) (run d q).
Example percent_rank_types :
  (is_double PostgreSQL (ranks w_percent_rank), is_double MySQL (ranks w_cume_dist),
   is_double SQLite (ranks w_percent_rank), is_double OceanBaseOracle (ranks w_percent_rank)) = (true, true, true, false).
Proof. check. Qed.
Example percent_rank_mariadb :
  result_is MariaDB (ranks w_percent_rank) 2
    [["1"; "0.0000000000"]; ["2"; "0.2500000000"]; ["2"; "0.2500000000"]; ["3"; "0.7500000000"]; ["5"; "1.0000000000"]]
  = true.
Proof. check. Qed.

(** MariaDB's [MEDIAN (x) OVER ()]: a double of 10 decimals ([win_percentile.result]; TODO 8.37) *)
Example median_mariadb :
  result_is MariaDB (window five [w_as (w_agg "median" (col c0) whole_partition) [] [] c1]) 2
    [["1"; "2.0000000000"]; ["2"; "2.0000000000"]; ["2"; "2.0000000000"]; ["3"; "2.0000000000"]; ["5"; "2.0000000000"]]
  = true.
Proof. check. Qed.
