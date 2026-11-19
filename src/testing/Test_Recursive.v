(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Tests of WITH RECURSIVE.                                                      *)
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

Definition db : db_state := init_db.

Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ db) (_instance _ db) (to_dialect d q).

Definition rows_of (d : vsem) (q : squery) (n : nat) : list (list string) :=
  map (fun t => map (fun i => show_value (dot (TD d) t (out_attr i))) (seq 0 n)) (run d q).

(** [WITH RECURSIVE t(c0) AS (VALUES (1) UNION ALL SELECT c0 + 1 FROM t WHERE c0 < 5) SELECT * FROM t] *)
Definition upto sq :=
  with_rec sq "t" (values_ [c0] [[int 1]])
    (select_where [as_ (fn "+" [col c0; int 1]) c0] [from_table "t"] (pred "<" [col c0; int 5]))
    (select_where [as_ (col c0) c0] [from_table "t"] c_true).

Example counting : 
  rows_of PostgreSQL (upto Set_All) 1 = [["1"]; ["2"]; ["3"]; ["4"]; ["5"]].
Proof. check. Qed.

Example counting_all_dialects : 
  map (fun d => rows_of d (upto Set_All) 1) 
      [MySQL; SQLite; OceanBaseMySQL; OceanBaseOracle] 
  = repeat [["1"]; ["2"]; ["3"]; ["4"]; ["5"]] 4.
Proof. check. Qed.

(** UNION (distinct) stops on a cycle: [c0 mod 3 + 1] from 1 visits 1, 2, 3 only. *)
Definition cycle :=
  with_rec Set_Distinct "t" (values_ [c0] [[int 1]])
    (select_where [as_ (fn "+" [fn "%" [col c0; int 3]; int 1]) c0] [from_table "t"] c_true)
    (select_where [as_ (col c0) c0] [from_table "t"] c_true).

Example cycle_terminates : rows_of PostgreSQL cycle 1 = [["1"]; ["2"]; ["3"]].
Proof. check. Qed.

(** The recursion is bounded: a recursion which does not reach a fixpoint within [rec_fuel] steps
    fails, as [cte_max_recursion_depth] makes MySQL fail (and PostgreSQL does not terminate). *)
Definition infinite :=
  with_rec Set_All "t" (values_ [c0] [[int 1]])
    (select_where [as_ (col c0) c0] [from_table "t"] c_true)
    (select_where [as_ (col c0) c0] [from_table "t"] c_true).

Definition fails (d : vsem) (q : squery) : bool :=
  match eval_query_result ORN (dialect_of d) (_basesort _ db) (_instance _ db) (to_dialect d q) with
  | QR_Error _ => true
  | _ => false
  end.

Example fuel : fails PostgreSQL infinite = true.
Proof. check. Qed.

Example no_fuel_needed : fails PostgreSQL (upto Set_All) = false.
Proof. check. Qed.

(** The body can use the table several times and the working table is the last step only. *)
Example fibonacci :
  rows_of PostgreSQL
    (with_rec Set_All "t" (values_ [c0; c1] [[int 0; int 1]])
       (select_where [as_ (col c1) c0; as_ (fn "+" [col c0; col c1]) c1] [from_table "t"] (pred "<" [col c1; int 20]))
       (select_where [as_ (col c0) c0] [from_table "t"] c_true)) 1
  = [["0"]; ["1"]; ["1"]; ["2"]; ["3"]; ["5"]; ["8"]; ["13"]].
Proof. check. Qed.

Example accepted_recursive :
  map (fun d => accepted_by (dialect_of d) (to_dialect d (upto Set_All)))
      [PostgreSQL; MySQL; SQLite; OceanBaseMySQL; OceanBaseOracle] = [true; true; true; true; true].
Proof. check. Qed.
