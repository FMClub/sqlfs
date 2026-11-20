(** * The new semantics ([SqlFull.v]) and the original one ([Sql.v]) agree on their common fragment (TODO 6.1)

    [to_full] translates the queries of [Sql.v] which are tables and [UNION ALL] of such queries to the syntax of
    [SqlFull.v]; on them, the two semantics give the same bag of tuples ([sql_full_agree]): [SqlFull.v]
    returns a list (its order is the one of the evaluation), [Sql.v] a bag. The statement assumes, as
    [union_all_spec], a dialect which does not convert the columns of a set operation ([unify_column] and
    [unify_rows] are the identity: PostgreSQL, SQLite) and operands of the same sort, which [Sql.v] requires too
    (it returns the empty bag otherwise). The fragment is the first step of I2: the selections, joins and
    grouping of [Sql.v] are the next ones. *)
Require Import List Bool.
Require Import BasicFacts ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection
        FlatData Bool3 Formula Sql SqlFull SqlFullFacts.

Section Sec.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.
Hypothesis ORN : Oset.Rcd relname.
Hypothesis O : dialect T.
Hypothesis basesort : relname -> Fset.set (Tuple.A T).
Hypothesis instance : relname -> Febag.bag (Fecol.CBag (Tuple.CTuple T)).

Import Tuple.

Notation BTupleT := (Fecol.CBag (CTuple T)).

(** the common fragment: tables and [UNION ALL] *)
Fixpoint to_full (q : sql_query T relname) : option (squery T relname) :=
  match q with
  | Sql_Table _ r => Some (SQ_Table _ r)
  | Sql_Set Union q1 q2 =>
    match to_full q1, to_full q2 with
    | Some a, Some b => Some (SQ_Set Union Set_All a b)
    | _, _ => None
    end
  | _ => None
  end.

(** the operands of each set operation have the same sort *)
Fixpoint well_sorted (q : sql_query T relname) : bool :=
  match q with
  | Sql_Table _ _ => true
  | Sql_Set _ q1 q2 =>
    Fset.equal (A T) (sql_sort basesort q1) (sql_sort basesort q2) && well_sorted q1 && well_sorted q2
  | _ => true
  end.

Lemma to_full_sort :
  forall q q', to_full q = Some q' -> squery_sort ORN basesort nil q' = sql_sort basesort q.
Proof.
intro q; induction q as [r | o q1 IH1 q2 IH2 | ]; intros q' H; simpl in H; try discriminate H.
- injection H; intros <-; reflexivity.
- destruct o; try discriminate H.
  case_eq (to_full q1); [intros a Ha | intro Ha]; rewrite Ha in H; [ | discriminate H].
  case_eq (to_full q2); [intros b Hb | intro Hb]; rewrite Hb in H; [ | discriminate H].
  injection H; intros <-; exact (IH1 a Ha).
Qed.

Theorem sql_full_agree :
  forall unknown contains_nulls env env' q q',
    (forall l, unify_column O l = l) ->
    (forall atts rows, unify_rows O atts rows = rows) ->
    to_full q = Some q' -> well_sorted q = true ->
    Febag.equal BTupleT (Febag.mk_bag BTupleT (eval_squery ORN O basesort instance nil env q'))
                (eval_sql_query basesort instance unknown contains_nulls env' q) = true.
Proof.
intros unknown contains_nulls env env' q; induction q as [r | o q1 IH1 q2 IH2 | ]; intros q' Hc Hu H W; simpl in H; try discriminate H.
- injection H; intros <-; simpl; apply Febag.elements_mk_bag.
- destruct o; try discriminate H.
  case_eq (to_full q1); [intros a Ha | intro Ha]; rewrite Ha in H; [ | discriminate H].
  case_eq (to_full q2); [intros b Hb | intro Hb]; rewrite Hb in H; [ | discriminate H].
  injection H; intros <-.
  simpl in W; rewrite !andb_true_iff in W; destruct W as [[S12 W1] W2].
  rewrite union_all_spec; trivial;
    [ | rewrite (to_full_sort _ _ Ha), (to_full_sort _ _ Hb); exact S12].
  rewrite eval_sql_query_unfold, S12; simpl.
  rewrite Febag.nb_occ_equal; intro t.
  rewrite Febag.nb_occ_mk_bag, Oeset.nb_occ_app, Febag.nb_occ_union.
  assert (K1 := IH1 a Hc Hu Ha W1); assert (K2 := IH2 b Hc Hu Hb W2).
  rewrite Febag.nb_occ_equal in K1, K2.
  rewrite <- (K1 t), <- (K2 t), !Febag.nb_occ_mk_bag; reflexivity.
Qed.

End Sec.
