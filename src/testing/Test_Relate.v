(** * The relation between [Sql.v] and [SqlFull.v] is not vacuous (TODO 8.29)

    [sql_full_agree3] ([SqlRelateSelect.v]) has hypotheses on the dialect. Here is a dialect of the instance of
    the tests which satisfies all of them ([paper]: the values are stored as they are, the functions, predicates
    and aggregates are those of the instance, nothing is converted), a database, and the instance of the theorem
    for a query with a selection and a [UNION ALL]. The aggregates which do not depend on the order of their input
    are the counts here ([perm_count]); the hypothesis on the aggregates ([Hperm]) is false for [string_agg], which
    is why it is stated for the aggregates of the query only. *)
Require Import List String ZArith Permutation.
Require Import Bool3 FlatData ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection Tree Formula Sql SqlFull
        SqlRelate SqlRelateSelect.
Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax.
Import Tuple.
Import NullValues.
Import ListNotations.
Open Scope string_scope.

Notation a := (Attr_Z "a").
Notation b := (Attr_Z "b").

(** the dialect: no value is taken for a NULL by the evaluation itself ([Hnull]: the NULLs of the instance have a
    type, so that no single NULL value exists), the predicates of the instance give the three-valued logic *)
Definition eq3p (v w : value) : bool3 :=
  match Oset.compare OVal v w with Eq => true3 | _ => false3 end.

Definition paper : dialect TNull :=
  mk_dialect TNull
             (fun _ => false) (Value_Z None) bool3_of_value value_of_bool3 eq3p sql_order
             (fun z => Value_Z (Some z)) rat_of_value value_of_rat (fun v => v) false
             (fun _ _ => true) (fun _ => true) (fun _ => true)
             (fun _ => false) Value_Err (Attr_string "#error")
             (fun _ => false) (fun _ _ => false) false (fun v => v) (fun _ => false)
             (fun _ => 0%nat) (fun _ _ l => l) (fun l => l) (fun _ => None)
             interp_symbol interp_predicate interp_aggregate.

(** the aggregates which count *)
Definition perm_count (ag : Values.aggregate) : bool :=
  match ag with Values.Aggregate s => String.eqb s "count" || String.eqb s "count(*)" end.

Lemma perm_filter : forall (X : Type) (f : X -> bool) l1 l2, Permutation l1 l2 -> Permutation (filter f l1) (filter f l2).
Proof.
intros X f l1 l2 P; induction P as [ | x l1 l2 P IH | x y l | l1 l2 l3 P1 IH1 P2 IH2]; simpl.
- constructor.
- destruct (f x); [constructor | ]; exact IH.
- destruct (f x); destruct (f y); try apply Permutation_refl; constructor.
- eapply perm_trans; eassumption.
Qed.

Lemma perm_count_ok : forall ag, perm_count ag = true ->
  forall l1 l2, Permutation l1 l2 -> interp_aggregate ag l1 = interp_aggregate ag l2.
Proof.
intros [s] H l1 l2 P; unfold perm_count in H; rewrite Coq.Bool.Bool.orb_true_iff, !String.eqb_eq in H.
assert (L : List.length (non_nulls (map widen l1)) = List.length (non_nulls (map widen l2)))
  by (apply Permutation_length; unfold non_nulls; apply perm_filter, Permutation_map; exact P).
destruct H as [-> | ->].
- change (Value_Z (Some (Z.of_nat (List.length (non_nulls (map widen l1))))) =
          Value_Z (Some (Z.of_nat (List.length (non_nulls (map widen l2)))))); rewrite L; reflexivity.
- change (Value_Z (Some (Z.of_nat (List.length (map widen l1)))) = Value_Z (Some (Z.of_nat (List.length (map widen l2))))).
  rewrite !map_length, (Permutation_length P); reflexivity.
Qed.

(** one table [t (a, b)] *)
Definition bs (r : relname) : Fset.set (A TNull) :=
  match r with Rel s => if String.eqb s "t" then Fset.mk_set (A TNull) [a; b] else Fset.empty (A TNull) end.
Definition rows : list (tuple TNull) := map (fun vs => combine [a; b] vs) [[VZ 1; VZ 2]; [VZ 3; VZ 4]; [VZ 3; VZ 4]].
Definition inst (r : relname) : Febag.bag (Fecol.CBag (CTuple TNull)) :=
  match r with
  | Rel s => if String.eqb s "t" then Febag.mk_bag (Fecol.CBag (CTuple TNull)) rows else Febag.empty (Fecol.CBag (CTuple TNull))
  end.

Notation BT := (Fecol.CBag (CTuple TNull)).

(** ** The hypotheses of the theorem *)

Lemma paper_canon : forall t u,
  Oeset.eq_bool (OTuple TNull) (canon_tuple paper t) (canon_tuple paper u) = Oeset.eq_bool (OTuple TNull) t u.
Proof.
assert (K : forall t, Oeset.eq_bool (OTuple TNull) (canon_tuple paper t) t = true).
{ intro t; rewrite Oeset.eq_bool_true_compare_eq; unfold canon_tuple; rewrite tuple_eq; split; [apply labels_mk_tuple | ].
  intros x Hx; rewrite dot_mk_tuple; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Hx; rewrite Hx; reflexivity. }
intros t u; rewrite (Oeset.eq_bool_eq_1 _ _ _ _ (K t)), (Oeset.eq_bool_eq_2 _ _ _ _ (K u)); reflexivity.
Qed.

Lemma paper_in_ok : in_ok TNull paper unknown3 (fun _ => false).
Proof. split; intros; reflexivity. Qed.

Lemma tables_sorted : well_sorted_sql_table TNull bs inst.
Proof.
intros [s] t H; unfold inst in H; unfold bs; destruct (String.eqb s "t").
- rewrite Febag.mem_mk_bag, Oeset.mem_bool_true_iff in H; destruct H as [t' [E I]].
  rewrite tuple_eq in E; rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 E)).
  unfold rows in I; simpl in I; repeat (destruct I as [<- | I]; [vm_compute; reflexivity | ]); contradiction I.
- rewrite Febag.empty_spec_weak in H; discriminate H.
Qed.

(** ** The instance

    [(SELECT * FROM t WHERE a < 3) UNION ALL (TABLE t)], and
    [SELECT * FROM t WHERE EXISTS (SELECT * FROM t WHERE a < 3)] *)
Definition tbl r := _From_Item (_Sql_Table (Rel r)) _Att_Ren_Star.
Definition small := _Sql_Pred (Predicate "<") [_A_Expr (__Sql_Dot a); _A_Expr (_CstZ (Some 3%Z))].
Definition q1 : sql_query TNull relname :=
  _Sql_Set Union (_Sql_Select _Select_Star [tbl "t"] small _Group_Fine _Sql_True) (_Sql_Table (Rel "t")).
Definition q2 : sql_query TNull relname :=
  _Sql_Select _Select_Star [tbl "t"]
    (@Sql_Exists TNull (sql_query TNull relname) (_Sql_Select _Select_Star [tbl "t"] small _Group_Fine _Sql_True))
    _Group_Fine _Sql_True.

Definition tr (q : sql_query TNull relname) := to_full3 TNull relname bs perm_count q.

Example q1_translates : match tr q1 with Some _ => true | None => false end = true.
Proof. vm_compute; reflexivity. Qed.
Example q2_translates : match tr q2 with Some _ => true | None => false end = true.
Proof. vm_compute; reflexivity. Qed.

(** the theorem for this dialect and this database: the hypotheses of [sql_full_agree3] hold together *)
Theorem relate_witness : forall q q', tr q = Some q' ->
  Febag.equal BT (Febag.mk_bag BT (eval_squery ORN paper bs inst nil nil q'))
              (eval_sql_query bs inst unknown3 (fun _ => false) nil q) = true.
Proof.
intros q q' H.
refine (sql_full_agree3 TNull relname ORN paper bs inst _ _ _ _ _ _ _ perm_count _ perm_count_ok _ paper_canon _
          unknown3 (fun _ => false) _ paper_in_ok tables_sorted q q' H nil nil (Rnil TNull relname)); try (intros; reflexivity).
- intros a0 v K; discriminate K.
- intros v w K; exact K.
Qed.

(** the two results, by computation: 4 rows (one from the selection, three from the table), and 3 rows *)
Example q1_rows : option_map (fun q' => List.length (eval_squery ORN paper bs inst nil nil q')) (tr q1) = Some 4%nat.
Proof. vm_compute; reflexivity. Qed.
Example q2_rows : option_map (fun q' => List.length (eval_squery ORN paper bs inst nil nil q')) (tr q2) = Some 3%nat.
Proof. vm_compute; reflexivity. Qed.
