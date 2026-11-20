(** Tests of the MariaDB dialect. *)

Require Import List String ZArith NArith.

Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.

Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax
        Dialects PostgreSQL MySQL SQLite OceanBase MariaDB SpecRunner.

Import Tuple.
Import ListNotations.
Open Scope string_scope.

Ltac check := vm_compute; reflexivity.

Notation c0 := (Attr_Z "c0").

Definition acceptance (q : squery) := 
  map (fun d => accepted_by (dialect_of d) (vs_supports d) (to_dialect d q)) [MySQL; MariaDB].

Definition nums := values_ [c0] [[int 1]; [int 2]].

Example maria_intersect_all : 
  acceptance (set_op_ Inter Set_All nums nums) = [true; true].
Proof. check. Qed.

Example maria_with_ties : 
  acceptance (fetch_first nums [o_by (col c0) Asc] None true false 1%N) = [false; true].
Proof. check. Qed.

Example maria_no_full_join : 
  acceptance (select_star_where [join J_Full (from_table "p") (from_table "q") c_true] c_true) = [false; false].
Proof. check. Qed.

(** a bare column is accepted by MariaDB, not by MySQL *)
Example maria_bare_column :
  acceptance (select_grouped [as_ (col c0) c0; as_ (agg "count" (col c0)) (Attr_Z "c1")] [from_table "t"] (g_by [])) 
  = [false; true].
Proof. check. Qed.

(** PAD SPACE: trailing spaces are not significant in MariaDB (and in OceanBase), they are in MySQL 8 *)
Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).

Definition pad_query := 
  select_where [as_ (col c0) c0] [from_as nums [(c0, c0)]] (pred "=" [str "a"; str "a "]).

Example maria_pad_space :
  map (fun d => List.length (run d pad_query)) [MySQL; MariaDB; PostgreSQL] = [0%nat; 2%nat; 0%nat].
Proof. check. Qed.

(** * TiDB *)

Require Import TiDB.

Definition acceptance3 (q : squery) := 
  map (fun d => accepted_by (dialect_of d) (vs_supports d) (to_dialect d q)) [MySQL; MariaDB; TiDB].

Example tidb_full_join : 
  acceptance3 (select_star_where [join J_Full (from_table "p") (from_table "q") c_true] c_true) = [false; false; true].
Proof. check. Qed.

Example tidb_lateral : 
  acceptance3 (select_star_where [join_lateral J_Inner (from_table "p") (from_table "q") c_true] c_true) = [true; false; true].
Proof. check. Qed.

Example tidb_bare_column :
  acceptance3 (select_grouped [as_ (col c0) c0; as_ (agg "count" (col c0)) (Attr_Z "c1")] [from_table "t"] (g_by [])) 
  = [false; true; false].
Proof. check. Qed.

(** binary collation: case sensitive, PAD SPACE *)
Definition ci_query := 
  select_where [as_ (col c0) c0] [from_as nums [(c0, c0)]] (pred "=" [str "a"; str "A"]).

Example tidb_case_sensitive :
  map (fun d => List.length (run d ci_query)) [MySQL; MariaDB; TiDB] = [2%nat; 2%nat; 0%nat].
Proof. check. Qed.

Example tidb_pad_space :
  List.length (run TiDB pad_query) = 2%nat.
Proof. check. Qed.

(** * Percona and PolarDB *)

Require Import Percona PolarDB.

Definition acceptance_my (q : squery) := 
  map (fun d => accepted_by (dialect_of d) (vs_supports d) (to_dialect d q)) [MySQL; Percona; PolarDB].

Example polar_no_intersect : 
  acceptance_my (set_op_ Inter Set_Distinct nums nums) = [true; true; false].
Proof. check. Qed.

Example percona_is_mysql :
  map (fun d => List.length (run d pad_query)) [MySQL; Percona; PolarDB] = [0%nat; 0%nat; 0%nat].
Proof. check. Qed.
