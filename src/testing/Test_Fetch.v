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
