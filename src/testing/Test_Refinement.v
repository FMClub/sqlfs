(** * Refinement between dialects: Percona and MySQL (TODO 6.4)

    [percona_refines_mysql] ([Refinement.v]): the two dialects give the same rows to every query which does
    not call [VERSION ()]; a query which calls it tells them apart. *)
Require Import List String ZArith.
Require Import Bool3 FlatData ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.
Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax Dialects MySQL Percona Refinement SpecRunner.

Import Tuple.
Import ListNotations.
Open Scope string_scope.

Notation c0 := (Attr_Z "c0").

Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).

Definition text (d : vsem) (e : sexpr) : string :=
  match run d (select_where [as_ (fn "cast_string" [e]) c0] [] c_true) with
  | t :: nil => show_value (dot (TD d) t (out_attr 0))
  | _ => "?"
  end.

(** the counterexample: [VERSION ()] *)
Example version_percona : text Percona (fn "version" []) = "8.0.36-28". Proof. vm_compute; reflexivity. Qed.
Example version_mysql : text MySQL (fn "version" []) = "8.0.36". Proof. vm_compute; reflexivity. Qed.
Example version_calls : calls_version (select_where [as_ (fn "cast_string" [fn "version" []]) c0] [] c_true) = true.
Proof. vm_compute; reflexivity. Qed.

(** a query without [VERSION ()]: the theorem gives the same rows, whatever the database *)
Definition q_upper := select_where [as_ (fn "upper" [fn "concat" [str "a"; fn "database" []]]) c0] [] c_true.

Lemma q_upper_same : forall basesort instance,
  eval_query_list ORN (dialect_of Percona) basesort instance (to_dialect Percona q_upper) =
  eval_query_list ORN (dialect_of MySQL) basesort instance (to_dialect MySQL q_upper).
Proof. intros; apply percona_refines_mysql; vm_compute; reflexivity. Qed.

Example q_upper_text : text Percona (fn "upper" [fn "concat" [str "a"; fn "database" []]]) = "ATEST".
Proof. vm_compute; reflexivity. Qed.
