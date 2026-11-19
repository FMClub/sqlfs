(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Tests of the session variables of the MySQL family (TODO 1.10).               *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String ZArith NArith.

Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.

Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax
        Dialects ValueKit MySQL MariaDB TiDB SpecRunner Collation.

Import Tuple.
Import ListNotations.
Open Scope string_scope.

Ltac check := vm_compute; reflexivity.

Notation c0 := (Attr_Z "c0").

Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).

Definition value1 (d : vsem) (e : sexpr) : string :=
  match run d (select_where [as_ e c0] [] c_true) with
  | t :: nil => show_value (dot (TD d) t (out_attr 0))
  | _ => "?"
  end.

(** a session of MySQL with [PIPES_AS_CONCAT], [div_precision_increment] = 2, [group_concat_max_len] = 3,
    and without [ONLY_FULL_GROUP_BY] *)
Definition custom : my_session := mk_my_session false Coll_UCA900_AI_CI 2 true false 3%N 0.
Definition MySQL' : vsem := mysql_vs custom "MySQL" my_supports.

Example pipes_default : value1 MySQL (fn "||" [str "a"; str "b"]) = "0".
Proof. check. Qed.

Example pipes_as_concat : value1 MySQL' (fn "||" [str "a"; str "b"]) = "ab".
Proof. check. Qed.

Example div_incr_default : value1 MySQL (fn "/" [int 1; int 3]) = "0.3333".
Proof. check. Qed.

Example div_incr_2 : value1 MySQL' (fn "/" [int 1; int 3]) = "0.33".
Proof. check. Qed.

Definition abc := values_ [c0] [[str "a"]; [str "b"]; [str "c"]].

Definition concat_all := select_where [as_ (agg "group_concat" (col c0)) c0] [from_as abc [(c0, c0)]] c_true.

Example group_concat_default : map (fun t => show_value (dot (TD MySQL) t (out_attr 0))) (run MySQL concat_all) = ["a,b,c"].
Proof. check. Qed.

Example group_concat_truncated : map (fun t => show_value (dot (TD MySQL') t (out_attr 0))) (run MySQL' concat_all) = ["a,b"].
Proof. check. Qed.

Definition bare := select_grouped [as_ (col c0) c0; as_ (agg "count" (col c0)) (Attr_Z "c1")] [from_table "t"] (g_by []).

Example only_full_group_by :
  map (fun d => accepted_by (dialect_of d) (to_dialect d bare)) [MySQL; MySQL'; MariaDB; TiDB] = [false; true; true; false].
Proof. check. Qed.
