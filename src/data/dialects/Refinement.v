(** * Refinement between dialects (TODO 6.4)

    All the dialects evaluate their queries with the same instance of the values ([TD d] does not depend on
    [d]); a dialect differs from another one by the fields of its record [dialect_of d]. When two dialects
    have the same record except for the interpretations of the functions, predicates, aggregates and table
    functions ([same_core]), they give the same rows to every query on whose constructs they agree
    ([dialect_refinement], from [eval_congruence] of [SqlCongruence.v]).

    Percona Server for MySQL is MySQL with another name: its record differs from the one of MySQL only by
    the system function [VERSION ()] (["8.0.36-28"] and ["8.0.36"]), so that the two dialects give the same
    rows to every query which does not call [VERSION ()] ([percona_refines_mysql]), and only to those
    (the counterexample is in [Test_Refinement.v]). Acceptance is the same for both ([percona_accepts]). *)
Require Import List String Bool.
Require Import FlatData SqlFull SqlCongruence Values GenericInstance Dialects MySQL Percona.
Import ListNotations.
Open Scope string_scope.

(** the fields of the records of evaluation which are not interpretations of names *)
Definition same_core (d1 d2 : vsem) : Prop :=
  vs_is_null d2 = vs_is_null d1 /\ vs_truth d2 = vs_truth d1 /\ vs_of_truth d2 = vs_of_truth d1 /\
  vs_eq3 d2 = vs_eq3 d1 /\ vs_order d2 = vs_order d1 /\ vs_canon d2 = vs_canon d1 /\
  vs_nulls_smallest d2 = vs_nulls_smallest d1 /\ vs_scalar_first d2 = vs_scalar_first d1 /\
  vs_pred_error d2 = vs_pred_error d1 /\ vs_const d2 = vs_const d1 /\ vs_truth_error d2 = vs_truth_error d1 /\
  vs_cmp_coerce d2 = vs_cmp_coerce d1 /\ vs_unify d2 = vs_unify d1.

Lemma dialect_of_with : forall d1 d2, same_core d1 d2 ->
  dialect_of d2 =
  with_interp (TD d1) (dialect_of d1) (vs_interp_symbol d2) (vs_interp_predicate d2) (vs_interp_aggregate d2)
              (vs_table_fun d2) (vs_known_symbol d2) (vs_known_predicate d2) (vs_known_aggregate d2).
Proof.
intros d1 d2 [E1 [E2 [E3 [E4 [E5 [E6 [E7 [E8 [E9 [E10 [E11 [E12 E13]]]]]]]]]]]].
unfold dialect_of, with_interp; cbn.
rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13; reflexivity.
Qed.

(** [d2] agrees with [d1] on a construct *)
Definition agree_d (d1 d2 : vsem) : use (TD d1) -> Prop :=
  agree (TD d1) (dialect_of d1) (vs_interp_symbol d2) (vs_interp_predicate d2) (vs_interp_aggregate d2)
        (vs_table_fun d2).

Theorem dialect_refinement :
  forall d1 d2, same_core d1 d2 ->
  forall (rel : Type) ORN basesort instance (q : squery TNull rel),
    (forall u, In u (squery_uses (to_dialect d1 q)) -> agree_d d1 d2 u) ->
    forall ce env,
      eval_squery ORN (dialect_of d2) basesort instance ce env (to_dialect d2 q) =
      eval_squery ORN (dialect_of d1) basesort instance ce env (to_dialect d1 q).
Proof.
intros d1 d2 C rel ORN basesort instance q A ce env.
change (to_dialect d2 q) with (to_dialect d1 q).
rewrite (dialect_of_with d1 d2 C).
apply eval_congruence; exact A.
Qed.

(** * Percona and MySQL *)

Lemma percona_core : same_core MySQL Percona.
Proof. repeat split. Qed.

Lemma string_assoc_app : forall (X : Type) s (l1 l2 : list (string * X)),
  string_assoc X s (l1 ++ l2) = match string_assoc X s l1 with Some a => Some a | None => string_assoc X s l2 end.
Proof.
intros X s l1 l2; induction l1 as [ | [k v] l1 IH]; [reflexivity | ]; simpl.
destruct (String.eqb s k); [reflexivity | exact IH].
Qed.

(** the two tables of functions differ only at their first entry, [version] *)
Lemma percona_sys : exists vP vM X,
  sys_table default_env "Percona Server for MySQL" = ("version", vP) :: X /\
  sys_table default_env "MySQL" = ("version", vM) :: X.
Proof. do 3 eexists; split; reflexivity. Qed.

Lemma aliases_not_version : forallb (fun p => negb (String.eqb (snd p) "version")) my_aliases = true.
Proof. reflexivity. Qed.

Lemma assoc_other : forall (X : Type) s (v1 v2 : X) l, s <> "version" ->
  string_assoc X s (("version", v1) :: l) = string_assoc X s (("version", v2) :: l).
Proof. intros X s v1 v2 l H; simpl; apply String.eqb_neq in H; rewrite H; reflexivity. Qed.

Lemma percona_symb : forall s, s <> "version" -> vs_symb Percona s = vs_symb MySQL s.
Proof.
intros s Hs; destruct percona_sys as [vP [vM [X [EP EM]]]].
unfold Percona, MySQL, mysql_vs; cbn [vs_symb]; unfold table_of_list, with_my_aliases.
rewrite EP, EM.
set (C := my_closeout_funs ++ my_symbol_table).
cbn [app].
assert (K : forall k, k <> "version" ->
          string_assoc _ k (("version", vP) :: X ++ C) = string_assoc _ k (("version", vM) :: X ++ C)).
{ intros k Hk; apply assoc_other; exact Hk. }
rewrite !string_assoc_app with (l1 := ("version", _) :: X ++ C).
rewrite (K s Hs).
destruct (string_assoc _ s (("version", vM) :: X ++ C)); [reflexivity | ].
f_equal; [ | rewrite (K "cast_datetime") by discriminate; reflexivity].
assert (AV := aliases_not_version); induction my_aliases as [ | [a t] al IH]; [reflexivity | ].
simpl in AV |- *; apply andb_true_iff in AV; destruct AV as [A1 A2].
rewrite (K t) by (intro E; subst; discriminate).
rewrite (IH A2); reflexivity.
Qed.

(** the queries which call [VERSION ()] *)
Definition calls_version {rel : Type} (q : squery TNull rel) : bool :=
  existsb (fun u => match u with U_Symbol _ (Symbol _ "version") _ => true | _ => false end)
          (squery_uses (to_dialect MySQL q)).

Theorem percona_refines_mysql :
  forall (rel : Type) ORN basesort instance (q : squery TNull rel), calls_version q = false ->
  forall ce env,
    eval_squery ORN (dialect_of Percona) basesort instance ce env (to_dialect Percona q) =
    eval_squery ORN (dialect_of MySQL) basesort instance ce env (to_dialect MySQL q).
Proof.
intros rel ORN basesort instance q V; apply dialect_refinement; [exact percona_core | ].
intros u Hu; destruct u as [f | f n | name | p | a]; cbn [agree_d agree]; try reflexivity; [exact I | ].
destruct f as [s | v]; intros l _; [ | reflexivity].
assert (Hs : s <> "version").
{ intro E; subst s; unfold calls_version in V.
  assert (W : existsb (fun u => match u with U_Symbol _ (Symbol _ "version") _ => true | _ => false end)
                (squery_uses (to_dialect MySQL q)) = true)
    by (apply existsb_exists; exists (U_Symbol _ (Symbol _ "version") n); split; [exact Hu | reflexivity]).
  rewrite W in V; discriminate. }
unfold vs_interp_symbol; rewrite (percona_symb s Hs); reflexivity.
Qed.

(** Percona accepts the queries which MySQL accepts, and conversely: the arities and the constructs are
    those of MySQL, and the functions are the same names *)
Lemma percona_known : forall f n, vs_known_symbol Percona f n = vs_known_symbol MySQL f n.
Proof.
intros [s | v] n; [ | reflexivity]; unfold vs_known_symbol.
destruct (String.eqb s "version") eqn:E.
- apply String.eqb_eq in E; subst; reflexivity.
- apply String.eqb_neq in E; rewrite (percona_symb s E); reflexivity.
Qed.
