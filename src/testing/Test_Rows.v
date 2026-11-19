(** * Row values (TODO 3.7) *)
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
(** the truth value of a condition: [t], [f] or [u] (UNKNOWN, a row of [NOT c] is missing too) *)
Definition truth (d : vsem) (c : scond) : string :=
  match run d (select_where [as_ (int 1) c0] [] c), run d (select_where [as_ (int 1) c0] [] (c_not c)) with
  | _ :: _, _ => "t" | nil, _ :: _ => "f" | nil, nil => "u" end.

(** [(1, 2) < (1, 3)]: the first pair is equal, the second decides *)
Example row_lt : truth PostgreSQL (pred "row<" [int 1; int 2; int 1; int 3]) = "t".
Proof. check. Qed.
(** [(1, NULL) < (2, 0)]: decided by the first pair, the NULL does not matter *)
Example row_lt_null_after : truth MySQL (pred "row<" [int 1; cst NullZ; int 2; int 0]) = "t".
Proof. check. Qed.
(** [(1, NULL) < (1, 0)]: the NULL comes before the decision *)
Example row_lt_null : truth PostgreSQL (pred "row<" [int 1; cst NullZ; int 1; int 0]) = "u".
Proof. check. Qed.
Example row_le_eq : truth SQLite (pred "row<=" [int 1; int 2; int 1; int 2]) = "t".
Proof. check. Qed.
Example row_gt : truth PostgreSQL (pred "row>" [int 2; int 0; int 1; int 9]) = "t".
Proof. check. Qed.
(** [(NULL, NULL) IS NULL] is true, [(1, NULL) IS NULL] and [(1, NULL) IS NOT NULL] are false *)
Example row_is_null : truth PostgreSQL (pred "row is null" [cst NullZ; cst NullZ]) = "t".
Proof. check. Qed.
Example row_is_null_partial : truth PostgreSQL (pred "row is null" [int 1; cst NullZ]) = "f".
Proof. check. Qed.
Example row_is_not_null_partial : truth PostgreSQL (pred "row is not null" [int 1; cst NullZ]) = "f".
Proof. check. Qed.
(** [(DATE '2001-02-16', DATE '2001-12-21') OVERLAPS (DATE '2001-10-30', DATE '2002-10-30')] (PostgreSQL manual
    9.9) is true; [(DATE '2001-02-16', INTERVAL '100 days') OVERLAPS (DATE '2001-10-30', DATE '2002-10-30')] is false *)
Definition dt (t : string) := fn "cast_date" [str t].
Example overlaps_true : truth PostgreSQL (pred "overlaps" [dt "2001-02-16"; dt "2001-12-21"; dt "2001-10-30"; dt "2002-10-30"]) = "t".
Proof. check. Qed.
Example overlaps_interval : truth PostgreSQL (pred "overlaps" [dt "2001-02-16"; fn "cast_interval" [str "100 days"]; dt "2001-10-30"; dt "2002-10-30"]) = "f".
Proof. check. Qed.
(** [(DATE '2001-10-29', DATE '2001-10-30') OVERLAPS (DATE '2001-10-30', DATE '2001-10-31')]: false (an end is
    not in its period); with equal starts and empty periods: true *)
Example overlaps_touch : truth PostgreSQL (pred "overlaps" [dt "2001-10-29"; dt "2001-10-30"; dt "2001-10-30"; dt "2001-10-31"]) = "f".
Proof. check. Qed.
Example overlaps_same_start : truth PostgreSQL (pred "overlaps" [dt "2001-10-30"; dt "2001-10-30"; dt "2001-10-30"; dt "2001-10-31"]) = "t".
Proof. check. Qed.
