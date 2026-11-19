(** * Window functions: frame exclusion, rational [RANGE] offsets, [IGNORE NULLS], [FROM LAST] (TODO 3.1) *)
Require Import List String ZArith NArith QArith.
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
Notation c2 := (Attr_Z "c2").
Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).
Definition rows (d : vsem) (q : squery) (n : nat) : list (list string) :=
  map (fun t => map (fun i => show_value (dot (TD d) t (out_attr i))) (seq 0 n)) (run d q).
Definition result_is (d : vsem) (q : squery) (n : nat) (expected : list (list string)) : bool :=
  match_unordered (map (fun t => map (fun i => dot (TD d) t (out_attr i)) (seq 0 n)) (run d q)) expected.
Definition accepts (d : vsem) (q : squery) : bool := accepted_by (dialect_of d) (to_dialect d q).

Definition five := values_ [c0] [[int 1]; [int 2]; [int 3]; [int 4]; [int 5]].
Definition ties := values_ [c0] [[int 1]; [int 2]; [int 2]; [int 3]].

(** [EXCLUDE CURRENT ROW]: the sum of the neighbours (PostgreSQL manual 4.2.8) *)
Definition excl_sum t ex fr := window t [w_as (w_agg "sum" (col c0) (Frame_Excl fr ex)) [] [o_by (col c0) Asc] c1].
Example excl_current :
  result_is PostgreSQL (excl_sum five Excl_Current_Row (Frame_Rows (Preceding 1) (Following 1))) 2
    [["1"; "2"]; ["2"; "4"]; ["3"; "6"]; ["4"; "8"]; ["5"; "4"]] = true.
Proof. check. Qed.
(** [EXCLUDE GROUP] (the current row and its peers) and [EXCLUDE TIES] (its peers, not itself) over the
    whole partition *)
Example excl_group :
  result_is PostgreSQL (excl_sum ties Excl_Group (Frame_Rows Unbounded_Preceding Unbounded_Following)) 2
    [["1"; "7"]; ["2"; "4"]; ["2"; "4"]; ["3"; "5"]] = true.
Proof. check. Qed.
Example excl_ties :
  result_is PostgreSQL (excl_sum ties Excl_Ties (Frame_Rows Unbounded_Preceding Unbounded_Following)) 2
    [["1"; "8"]; ["2"; "6"]; ["2"; "6"]; ["3"; "8"]] = true.
Proof. check. Qed.
Example excl_no_others :
  result_is SQLite (excl_sum ties Excl_No_Others (Frame_Rows Unbounded_Preceding Unbounded_Following)) 2
    [["1"; "8"]; ["2"; "8"]; ["2"; "8"]; ["3"; "8"]] = true.
Proof. check. Qed.
(** MySQL has no frame exclusion *)
Example excl_mysql : accepts MySQL (excl_sum five Excl_Current_Row (Frame_Rows (Preceding 1) (Following 1))) = false.
Proof. check. Qed.

(** [RANGE BETWEEN 0.5 PRECEDING AND CURRENT ROW] over decimals *)
Definition decs := values_ [c0] [[cst (VD 10 1)]; [cst (VD 15 1)]; [cst (VD 20 1)]; [cst (VD 30 1)]].
Example range_decimal :
  result_is PostgreSQL (window decs [w_as (w_agg "count" (col c0) (Frame_Range (Preceding_Q (1 # 2)) Current_Row)) [] [o_by (col c0) Asc] c1]) 2
    [["1.0"; "1"]; ["1.5"; "2"]; ["2.0"; "2"]; ["3.0"; "1"]] = true.
Proof. check. Qed.
(** [RANGE BETWEEN INTERVAL '1 day' PRECEDING AND CURRENT ROW] over dates: the offset in days *)
Definition dates := values_ [c0] [[fn "cast_date" [str "2024-01-01"]]; [fn "cast_date" [str "2024-01-02"]];
                                  [fn "cast_date" [str "2024-01-04"]]; [fn "cast_date" [str "2024-01-05"]]].
Example range_dates :
  map (fun r => nth 1 r "") (rows PostgreSQL (window dates [w_as (w_agg "count" (col c0) (Frame_Range (Preceding_Q 1) Current_Row)) [] [o_by (col c0) Asc] c1]) 2)
  = ["1"; "2"; "1"; "2"].
Proof. check. Qed.

(** [IGNORE NULLS] and [FROM LAST] (Oracle) *)
Definition gaps := values_ [c0; c2] [[int 1; cst NullZ]; [int 2; int 20]; [int 3; cst NullZ]; [int 4; int 40]].
Definition w_on (f : swfun TNull relname) := window gaps [w_as f [] [o_by (col c0) Asc] c1].
Definition col1 (d : vsem) (q : squery) : list string := map (fun r => nth 1 r "") (rows d q 2).

Example lag_ignore : col1 OceanBaseOracle (w_on (w_opts (w_lag (col c2) 1 (cst NullZ)) true false)) = ["NULL"; "NULL"; "20"; "20"].
Proof. check. Qed.
Example lag_respect : col1 OceanBaseOracle (w_on (w_lag (col c2) 1 (cst NullZ))) = ["NULL"; "NULL"; "20"; "NULL"].
Proof. check. Qed.
Example first_ignore : col1 OceanBaseOracle (w_on (w_opts (w_first_value (col c2) default_frame) true false)) = ["NULL"; "20"; "20"; "20"].
Proof. check. Qed.
Example last_ignore : col1 OceanBaseOracle (w_on (w_opts (w_last_value (col c2) whole_partition) true false)) = ["40"; "40"; "40"; "40"].
Proof. check. Qed.
Example nth_from_last : col1 OceanBaseOracle (w_on (w_opts (w_nth_value (col c2) 2 whole_partition) false true)) = ["NULL"; "NULL"; "NULL"; "NULL"].
Proof. check. Qed.
Example nth_from_last_ignore : col1 OceanBaseOracle (w_on (w_opts (w_nth_value (col c2) 2 whole_partition) true true)) = ["20"; "20"; "20"; "20"].
Proof. check. Qed.
(** PostgreSQL rejects [IGNORE NULLS] *)
Example pg_ignore : accepts PostgreSQL (w_on (w_opts (w_lag (col c2) 1 (cst NullZ)) true false)) = false.
Proof. check. Qed.
