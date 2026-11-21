(** * The new semantics ([SqlFull.v]) and the original one ([Sql.v]) agree on their common fragment (TODO 6.1)

    [to_full] translates the queries of [Sql.v] which are tables and set operations of such queries (the bag
    operations of [Sql.v]: [UNION ALL], [INTERSECT ALL], [EXCEPT ALL] and the maximum of the multiplicities)
    to the syntax of [SqlFull.v]; on them, the two semantics give the same bag of tuples ([sql_full_agree]):
    [SqlFull.v] returns a list (its order is the one of the evaluation), [Sql.v] a bag. The statement
    assumes
    - a dialect which does not convert the columns of a set operation ([unify_rows] is the identity:
      PostgreSQL, SQLite),
    - whose canonical form of values identifies only equal tuples ([Hcanon]: [SqlFull.v] counts the
      occurrences of a tuple in [INTERSECT ALL] and [EXCEPT ALL] up to it, [Sql.v] up to equality),
    - stored rows without error values ([Herr]: [SqlFull.v] keeps the failed rows of the operands),
    - and operands of the same sort, which [Sql.v] requires too (it returns the empty bag otherwise).
    The selections, joins and grouping of [Sql.v] are the next steps of I2. *)
Require Import List Bool NArith Lia.
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

(** ** Multiplicities

    [SqlFull.v] counts the occurrences of a tuple up to its canonical form ([tuple_count], through
    [canon_tuple]), [Sql.v] up to the equality of tuples. They agree for a dialect whose canonical form does
    not identify tuples which are not equal ([Hcanon]): the statements below assume it. *)
Section Count.

Hypothesis Hcanon :
  forall t u, Oeset.eq_bool (OTuple T) (canon_tuple O t) (canon_tuple O u) = Oeset.eq_bool (OTuple T) t u.

Lemma tuple_count_nb_occ :
  forall u l, N.of_nat (tuple_count O u l) = Oeset.nb_occ (OTuple T) u l.
Proof.
intros u l; induction l as [ | a l IH]; [reflexivity | ].
unfold tuple_count in *; rewrite Oeset.nb_occ_unfold; cbn [filter]; rewrite Hcanon, <- IH.
unfold Oeset.eq_bool at 1; destruct (Oeset.compare (OTuple T) u a); cbn [length]; lia.
Qed.

Lemma tuple_count_eq :
  forall t u l, Oeset.eq_bool (OTuple T) t u = true -> tuple_count O t l = tuple_count O u l.
Proof.
intros t u l H; induction l as [ | a l IH]; [reflexivity | ].
unfold tuple_count in *; simpl; rewrite 2 Hcanon, (Oeset.eq_bool_eq_1 _ _ _ _ H).
destruct (Oeset.eq_bool (OTuple T) u a); simpl; rewrite IH; reflexivity.
Qed.

Lemma tuple_count_cons :
  forall u t l,
    tuple_count O u (t :: l) = ((if Oeset.eq_bool (OTuple T) u t then 1 else 0) + tuple_count O u l)%nat.
Proof.
intros u t l; unfold tuple_count; cbn [filter]; rewrite Hcanon.
destruct (Oeset.eq_bool (OTuple T) u t); reflexivity.
Qed.

Lemma tuple_count_app :
  forall u l1 l2, tuple_count O u (l1 ++ l2) = (tuple_count O u l1 + tuple_count O u l2)%nat.
Proof.
intros u l1 l2; unfold tuple_count; rewrite filter_app, app_length; reflexivity.
Qed.

(** the multiplicity of [u] in [filter_occ keep before l]: the number of the occurrences [i] of [u] in [l],
    counted from those in [before], which [keep] retains *)
Lemma tuple_count_filter_occ :
  forall keep, (forall i t u, Oeset.eq_bool (OTuple T) t u = true -> keep i t = keep i u) ->
  forall l before u,
    tuple_count O u (filter_occ O keep before l) =
    List.length (filter (fun i => keep i u) (seq (tuple_count O u before) (tuple_count O u l))).
Proof.
intros keep Hk l; induction l as [ | t l IH]; intros before u; [reflexivity | ].
cbn [filter_occ]; rewrite tuple_count_app, IH, 2 tuple_count_cons.
case_eq (Oeset.eq_bool (OTuple T) u t); intro E.
- assert (E' : Oeset.eq_bool (OTuple T) t u = true)
    by (destruct (Oeset.Equivalence (OTuple T)) as [_ Sym _]; apply Sym; exact E).
  rewrite (tuple_count_eq _ _ before E'), (Hk _ _ _ E').
  destruct (keep (tuple_count O u before) u) eqn:K; cbn [List.length plus];
    [rewrite tuple_count_cons, E | ]; cbn [seq filter]; rewrite K; reflexivity.
- destruct (keep (tuple_count O t before) t); [rewrite tuple_count_cons, E | ]; reflexivity.
Qed.

Lemma count_lt :
  forall c n, List.length (filter (fun i => Nat.ltb i c) (seq 0 n)) = Nat.min n c.
Proof.
intros c n; induction n as [ | n IH]; [reflexivity | ].
rewrite seq_S, filter_app, app_length, IH; cbn [filter plus].
destruct (Nat.ltb n c) eqn:H; [apply PeanoNat.Nat.ltb_lt in H | apply PeanoNat.Nat.ltb_ge in H]; cbn [List.length]; lia.
Qed.

Lemma count_ge :
  forall c n, List.length (filter (fun i => Nat.leb c i) (seq 0 n)) = (n - c)%nat.
Proof.
intros c n; induction n as [ | n IH]; [reflexivity | ].
rewrite seq_S, filter_app, app_length, IH; cbn [filter plus].
destruct (Nat.leb c n) eqn:H; [apply PeanoNat.Nat.leb_le in H | apply PeanoNat.Nat.leb_gt in H]; cbn [List.length]; lia.
Qed.

(** the multiplicities of the bag operations of [ALL]: sum, minimum, difference and maximum *)
Lemma eval_set_op_all_count :
  forall o l1 l2 u,
    N.of_nat (tuple_count O u (eval_set_op O o Set_All l1 l2)) =
    match o with
    | Union => (Oeset.nb_occ (OTuple T) u l1 + Oeset.nb_occ (OTuple T) u l2)%N
    | UnionMax => N.max (Oeset.nb_occ (OTuple T) u l1) (Oeset.nb_occ (OTuple T) u l2)
    | Inter => N.min (Oeset.nb_occ (OTuple T) u l1) (Oeset.nb_occ (OTuple T) u l2)
    | Diff => (Oeset.nb_occ (OTuple T) u l1 - Oeset.nb_occ (OTuple T) u l2)%N
    end.
Proof.
intros o l1 l2 u; rewrite <- 2 tuple_count_nb_occ.
destruct o; simpl eval_set_op.
- rewrite tuple_count_app; lia.
- rewrite tuple_count_app, tuple_count_filter_occ;
    [ | intros i t v H; rewrite (tuple_count_eq _ _ _ H); reflexivity].
  simpl tuple_count at 2; rewrite count_ge; lia.
- rewrite tuple_count_filter_occ; [ | intros i t v H; rewrite (tuple_count_eq _ _ _ H); reflexivity].
  simpl tuple_count at 1; rewrite count_lt; lia.
- rewrite tuple_count_filter_occ; [ | intros i t v H; rewrite (tuple_count_eq _ _ _ H); reflexivity].
  simpl tuple_count at 1; rewrite count_ge; lia.
Qed.

End Count.

(** the common fragment: tables and the set operations of [Sql.v], which are bag operations
    ([UNION ALL], [INTERSECT ALL], [EXCEPT ALL] and the maximum of multiplicities) *)
Fixpoint to_full (q : sql_query T relname) : option (squery T relname) :=
  match q with
  | Sql_Table _ r => Some (SQ_Table _ r)
  | Sql_Set o q1 q2 =>
    match to_full q1, to_full q2 with
    | Some a, Some b => Some (SQ_Set o Set_All a b)
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
- case_eq (to_full q1); [intros a Ha | intro Ha]; rewrite Ha in H; [ | discriminate H].
  case_eq (to_full q2); [intros b Hb | intro Hb]; rewrite Hb in H; [ | discriminate H].
  injection H; intros <-; exact (IH1 a Ha).
Qed.

Lemma filter_occ_incl :
  forall keep before l t, In t (filter_occ O keep before l) -> In t l.
Proof.
intros keep before l; revert before; induction l as [ | a l IH]; intros before t H; [contradiction H | ].
cbn [filter_occ] in H; apply in_app_or in H; destruct H as [H | H].
- destruct (keep _ a); [destruct H as [H | H]; [left; exact H | contradiction H] | contradiction H].
- right; exact (IH _ _ H).
Qed.

Lemma eval_set_op_incl :
  forall o l1 l2 t, In t (eval_set_op O o Set_All l1 l2) -> In t l1 \/ In t l2.
Proof.
intros o l1 l2 t H; destruct o; simpl in H.
- apply in_app_or; exact H.
- apply in_app_or in H; destruct H as [H | H]; [left | right; apply (filter_occ_incl _ _ _ _ H)]; exact H.
- left; apply (filter_occ_incl _ _ _ _ H).
- left; apply (filter_occ_incl _ _ _ _ H).
Qed.

Lemma keep_errors_clean :
  forall r all, (forall t, In t all -> row_error O t = false) -> keep_errors O r all = r.
Proof.
intros r all H; unfold keep_errors.
destruct (existsb (row_error O) r); [reflexivity | ].
rewrite existsb_false_filter; [apply app_nil_r | ].
clear r; induction all as [ | a all IHa]; [reflexivity | ].
simpl; rewrite (H a (or_introl eq_refl)); apply IHa; intros t Ht; apply H; right; exact Ht.
Qed.

(** ** The columns of a set operation

    For a dialect which does not convert the columns of a set operation ([Hun]), [unify_rows] gives the same
    rows, up to the equality of tuples (the tuples are built again: they are not the same terms, which is why the
    statement is not an equality of lists). *)
Section Unify.

Hypothesis Hun : forall l, unify_column O l = l.

Lemma unify_rows_eq : forall atts rows, Forall2 (fun t' t => t' =t= t) (unify_rows O atts rows) rows.
Proof.
intros atts rows; unfold unify_rows.
set (cols := map (fun a => (a, unify_column O (map (fun t => dot T t a) rows))) atts).
assert (G : forall rest n, (forall i t, nth_error rest i = Some t -> nth_error rows (n + i) = Some t) ->
  Forall2 (fun t' t => t' =t= t)
    (map (fun it : nat * tuple T =>
            let (i, t) := it in
            mk_tuple T (labels T t)
              (fun x => match find (fun c : attribute T * list (value T) => Oset.eq_bool (OAtt T) (fst c) x) cols with
                        | Some (_, vs) => nth i vs (dot T t x)
                        | None => dot T t x
                        end)) (combine (seq n (length rest)) rest)) rest).
{ intro rest; induction rest as [ | t rest IH]; intros n Hn; [constructor | ].
  cbn [length seq combine map]; constructor.
  - rewrite tuple_eq; split; [apply labels_mk_tuple | ].
    intros x Hx; rewrite dot_mk_tuple.
    rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Hx; rewrite Hx.
    case_eq (find (fun c : attribute T * list (value T) => Oset.eq_bool (OAtt T) (fst c) x) cols); [ | intros; reflexivity].
    intros [a vs] Hf; destruct (find_some _ _ Hf) as [Hin Ha]; simpl in Ha.
    rewrite Oset.eq_bool_true_iff in Ha; subst a.
    unfold cols in Hin; rewrite in_map_iff in Hin; destruct Hin as [b [Eb _]]; injection Eb; intros Ev Ex; subst b.
    rewrite Hun in Ev; subst vs.
    assert (K := Hn 0%nat t eq_refl); rewrite PeanoNat.Nat.add_0_r in K.
    apply nth_error_nth; rewrite (map_nth_error _ _ _ K); reflexivity.
  - apply IH; intros i u Hu; replace (S n + i)%nat with (n + S i)%nat by (rewrite PeanoNat.Nat.add_succ_r; reflexivity).
    apply Hn; exact Hu. }
exact (G rows 0%nat (fun i t H => H)).
Qed.

(** the bag of rows which are equal one by one *)
Lemma eq_rows_bag : forall l1 l2, Forall2 (fun t' t : tuple T => t' =t= t) l1 l2 ->
  Febag.equal BTupleT (Febag.mk_bag BTupleT l1) (Febag.mk_bag BTupleT l2) = true.
Proof.
intros l1 l2 H; rewrite Febag.nb_occ_equal; intro t; rewrite !Febag.nb_occ_mk_bag.
induction H as [ | x y l1 l2 Hxy H IH]; [reflexivity | ].
rewrite !(Oeset.nb_occ_unfold _ _ (_ :: _)), IH; f_equal.
case_eq (Oeset.compare (OTuple T) t y); intro K.
- rewrite (Oeset.compare_eq_trans _ _ _ _ K (Oeset.compare_eq_sym _ _ _ Hxy)); reflexivity.
- rewrite (Oeset.compare_lt_eq_trans _ _ _ _ K (Oeset.compare_eq_sym _ _ _ Hxy)); reflexivity.
- rewrite Oeset.compare_lt_gt, CompOpp_iff in K; simpl in K.
  rewrite Oeset.compare_lt_gt, (Oeset.compare_eq_lt_trans _ _ _ _ Hxy K); reflexivity.
Qed.

Lemma unify_rows_bag : forall atts rows,
  Febag.equal BTupleT (Febag.mk_bag BTupleT (unify_rows O atts rows)) (Febag.mk_bag BTupleT rows) = true.
Proof. intros; apply eq_rows_bag, unify_rows_eq. Qed.

(** a failed row is one up to the equality of tuples *)
Lemma row_error_teq : forall t u, t =t= u -> row_error O t = row_error O u.
Proof.
intros t u H; rewrite tuple_eq in H; destruct H as [Hl Hd]; unfold row_error.
rewrite <- (Fset.elements_spec1 _ _ _ Hl).
assert (K : forall a, In a ({{{labels T t}}}) -> is_error O (dot T t a) = is_error O (dot T u a)).
{ intros a Ha; rewrite (Hd a (Fset.in_elements_mem _ _ _ Ha)); reflexivity. }
induction ({{{labels T t}}}) as [ | a l IH]; [reflexivity | ].
simpl; rewrite (K a (or_introl eq_refl)), IH; [reflexivity | intros b Hb; apply K; right; exact Hb].
Qed.

(** the rows of [unify_rows] hold no error when the rows do not *)
Lemma unify_rows_clean : forall atts rows, (forall u, In u rows -> row_error O u = false) ->
  forall t, In t (unify_rows O atts rows) -> row_error O t = false.
Proof.
intros atts rows H t Ht; assert (K := unify_rows_eq atts rows).
induction K as [ | x y l1 l2 Hxy K IH]; [contradiction Ht | ].
destruct Ht as [E | Ht]; [subst x; rewrite (row_error_teq _ _ Hxy); apply H; left; reflexivity | ].
apply IH; [intros u Hu; apply H; right; exact Hu | exact Ht].
Qed.

End Unify.

Section Agree.

Hypothesis Hcanon :
  forall t u, Oeset.eq_bool (OTuple T) (canon_tuple O t) (canon_tuple O u) = Oeset.eq_bool (OTuple T) t u.
Hypothesis Hun : forall l, unify_column O l = l.
(** the stored rows hold no error value *)
Hypothesis Herr : forall r t, In t (Febag.elements BTupleT (instance r)) -> row_error O t = false.

Lemma to_full_clean :
  forall env q q', to_full q = Some q' ->
    forall t, In t (eval_squery ORN O basesort instance nil env q') -> row_error O t = false.
Proof.
intros env q; induction q as [r | o q1 IH1 q2 IH2 | ]; intros q' H; simpl in H; try discriminate H.
- injection H; intros <- t Ht; exact (Herr r t Ht).
- case_eq (to_full q1); [intros a Ha | intro Ha]; rewrite Ha in H; [ | discriminate H].
  case_eq (to_full q2); [intros b Hb | intro Hb]; rewrite Hb in H; [ | discriminate H].
  injection H; intros <- t Ht.
  change (In t (if Fset.equal (A T) (squery_sort ORN basesort nil a) (squery_sort ORN basesort nil b)
                then unify_rows O ({{{squery_sort ORN basesort nil a}}})
                       (keep_errors O (eval_set_op O o Set_All (eval_squery ORN O basesort instance nil env a)
                                                   (eval_squery ORN O basesort instance nil env b))
                                    (eval_squery ORN O basesort instance nil env a ++
                                     eval_squery ORN O basesort instance nil env b))
                else nil)) in Ht.
  destruct (Fset.equal _ _ _); [ | contradiction Ht].
  assert (C : forall u, In u (eval_squery ORN O basesort instance nil env a ++ eval_squery ORN O basesort instance nil env b) ->
              row_error O u = false)
    by (intros u Hu'; destruct (in_app_or _ _ _ Hu') as [K | K]; [exact (IH1 _ Ha _ K) | exact (IH2 _ Hb _ K)]).
  apply (unify_rows_clean Hun _ _) in Ht; [exact Ht | ].
  intros u Hu'; rewrite keep_errors_clean in Hu'; [ | exact C].
  destruct (eval_set_op_incl _ _ _ _ Hu') as [K | K]; [exact (IH1 _ Ha _ K) | exact (IH2 _ Hb _ K)].
Qed.

Theorem sql_full_agree :
  forall unknown contains_nulls env env' q q',
    to_full q = Some q' -> well_sorted q = true ->
    Febag.equal BTupleT (Febag.mk_bag BTupleT (eval_squery ORN O basesort instance nil env q'))
                (eval_sql_query basesort instance unknown contains_nulls env' q) = true.
Proof.
intros unknown contains_nulls env env' q; induction q as [r | o q1 IH1 q2 IH2 | ]; intros q' H W;
  simpl in H; try discriminate H.
- injection H; intros <-; simpl; apply Febag.elements_mk_bag.
- case_eq (to_full q1); [intros a Ha | intro Ha]; rewrite Ha in H; [ | discriminate H].
  case_eq (to_full q2); [intros b Hb | intro Hb]; rewrite Hb in H; [ | discriminate H].
  injection H; intros <-.
  simpl in W; rewrite !andb_true_iff in W; destruct W as [[S12 W1] W2].
  assert (S' : Fset.equal (A T) (squery_sort ORN basesort nil a) (squery_sort ORN basesort nil b) = true)
    by (rewrite (to_full_sort _ _ Ha), (to_full_sort _ _ Hb); exact S12).
  change (Febag.equal BTupleT (Febag.mk_bag BTupleT
            (if Fset.equal (A T) (squery_sort ORN basesort nil a) (squery_sort ORN basesort nil b)
             then unify_rows O ({{{squery_sort ORN basesort nil a}}})
                    (keep_errors O (eval_set_op O o Set_All (eval_squery ORN O basesort instance nil env a)
                                                (eval_squery ORN O basesort instance nil env b))
                                 (eval_squery ORN O basesort instance nil env a ++
                                  eval_squery ORN O basesort instance nil env b))
             else nil))
            (eval_sql_query basesort instance unknown contains_nulls env' (Sql_Set o q1 q2)) = true).
  rewrite S', (Febag.equal_eq_1 _ _ _ _ (unify_rows_bag Hun _ _)), keep_errors_clean;
    [ | intros u Hu'; destruct (in_app_or _ _ _ Hu') as [K | K];
        [exact (to_full_clean _ _ _ Ha _ K) | exact (to_full_clean _ _ _ Hb _ K)]].
  set (R := eval_set_op O o Set_All _ _).
  rewrite eval_sql_query_unfold, S12; simpl.
  rewrite Febag.nb_occ_equal; intro t.
  assert (K1 := IH1 a Ha W1); assert (K2 := IH2 b Hb W2).
  rewrite Febag.nb_occ_equal in K1, K2.
  unfold R; rewrite Febag.nb_occ_mk_bag, <- (tuple_count_nb_occ Hcanon t (eval_set_op O o Set_All _ _)),
  (eval_set_op_all_count Hcanon).
  unfold Febag.interp_set_op; destruct o;
    rewrite ?Febag.nb_occ_union_max, ?Febag.nb_occ_union, ?Febag.nb_occ_inter, ?Febag.nb_occ_diff;
    rewrite <- (K1 t), <- (K2 t), !Febag.nb_occ_mk_bag; reflexivity.
Qed.

End Agree.

End Sec.
