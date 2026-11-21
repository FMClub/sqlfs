(** * The sort of the rows of a query (TODO 6.2)

    Every row of the result of a query has the attributes of the sort of the query ([squery_sort]), and a
    failed row has the attribute [err_attr] besides ([err_row]): [srow (squery_sort ce q) t] for each row [t] of
    [eval_squery ce env q] ([eval_sorts]), when the stored relations hold rows of their sorts ([inst_ok]), and the
    recursive term of a [WITH RECURSIVE] has the sort of its base ([rec_ok]); the operands of a set operation
    of different sorts give no row. *)
Require Import List Bool NArith.
Require Import BasicFacts ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection FlatData SqlFull SqlInduction
        SqlFullFacts SqlGroupFacts.

Section Lists.

Variable X : Type.

Lemma In_firstn : forall n (l : list X) x, In x (firstn n l) -> In x l.
Proof.
intro n; induction n as [ | n IH]; intros [ | a l] x H; try contradiction.
destruct H as [<- | H]; [left; reflexivity | right; exact (IH l x H)].
Qed.

Lemma In_skipn : forall n (l : list X) x, In x (skipn n l) -> In x l.
Proof.
intro n; induction n as [ | n IH]; intros [ | a l] x H; try exact H; try contradiction.
right; exact (IH l x H).
Qed.

Lemma in_merge : forall le (l1 l2 : list X) x, In x (merge le l1 l2) -> In x l1 \/ In x l2.
Proof.
intros le l1; induction l1 as [ | a l1 IH1]; intros l2 x; [intro H; right; destruct l2; exact H | ].
induction l2 as [ | b l2 IH2]; intro H; [left; exact H | ].
simpl in H; destruct (le a b); destruct H as [<- | H].
- left; left; reflexivity.
- destruct (IH1 _ _ H) as [K | K]; [left; right; exact K | right; exact K].
- right; left; reflexivity.
- destruct (IH2 H) as [K | K]; [left; exact K | right; right; exact K].
Qed.

Lemma in_msort_fuel : forall le n (l : list X) x, In x (msort_fuel le n l) -> In x l.
Proof.
intros le n; induction n as [ | n IH]; intros l x H; [exact H | ].
destruct l as [ | a [ | b l]]; try exact H.
cbn [msort_fuel] in H; apply in_merge in H; destruct H as [H | H]; apply IH in H;
  [apply (In_firstn _ _ _ H) | apply (In_skipn _ _ _ H)].
Qed.

Lemma in_offset_limit : forall off lim (l : list X) x, In x (offset_limit off lim l) -> In x l.
Proof.
intros off lim l x; unfold offset_limit; intro H.
assert (K : forall k : list X, In x (match lim with Some n => firstn (N.to_nat n) k | None => k end) -> In x k)
  by (intros k; destruct lim; [apply In_firstn | exact (fun h => h)]).
apply K in H; destruct off; [exact (In_skipn _ _ _ H) | exact H].
Qed.

End Lists.

Section Sec.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.
Hypothesis ORN : Oset.Rcd relname.
Hypothesis O : dialect T.

Import Tuple.

Notation mem a s := (Fset.mem (A T) a s).

Notation setA := (Fset.set (A T)).
Notation tuple := (tuple T).
Notation BTupleT := (Fecol.CBag (CTuple T)).
Notation bagT := (Febag.bag BTupleT).

Hypothesis basesort : relname -> setA.
Hypothesis instance : relname -> bagT.

(** the row [t] has the sort [sa]; a failed row has the attribute [err_attr] and some of the attributes of [sa]
    (the failed row of an operand of a product keeps the attributes of its operand) *)
Definition srow (sa : setA) (t : tuple) : Prop :=
  (forall a, mem a (labels T t) = mem a sa) \/
  (mem (err_attr O) (labels T t) = true /\
   forall a, mem a (labels T t) = true -> mem a sa = true \/ a = err_attr O).

Lemma mem_labels_mk_tuple : forall s f a, mem a (labels T (mk_tuple T s f)) = mem a s.
Proof. intros s f a; apply Fset.mem_eq_2; apply labels_mk_tuple. Qed.

Lemma eq_bool_err : forall a, Oset.eq_bool (OAtt T) a (err_attr O) = true <-> a = err_attr O.
Proof.
intro a; unfold Oset.eq_bool; generalize (Oset.eq_bool_ok (OAtt T) a (err_attr O)); unfold Oset.eq_bool.
destruct (Oset.compare (OAtt T) a (err_attr O)); intro H; split; intro K; try discriminate; try reflexivity;
  try exact H; contradiction.
Qed.

Lemma srow_eq : forall s1 s2 t, (forall a, mem a s1 = mem a s2) -> srow s1 t -> srow s2 t.
Proof.
intros s1 s2 t E [H | [H1 H2]]; [left; intro a; rewrite H, E; reflexivity | right; split; [exact H1 | ]].
intros a Ha; rewrite <- E; exact (H2 a Ha).
Qed.

Lemma srow_sub : forall s1 s2 t, (forall a, mem a s1 = true -> mem a s2 = true) ->
  mem (err_attr O) (labels T t) = true -> srow s1 t -> srow s2 t.
Proof.
intros s1 s2 t E He [H | [H1 H2]]; right; split; trivial.
- intros a Ha; rewrite H in Ha; left; apply E; exact Ha.
- intros a Ha; destruct (H2 a Ha) as [K | K]; [left; apply E; exact K | right; exact K].
Qed.

Lemma err_labels : forall t a, mem a (labels T (err_row O t)) = mem a (labels T t) || Oset.eq_bool (OAtt T) a (err_attr O).
Proof. intros t a; unfold err_row; rewrite mem_labels_mk_tuple, Fset.mem_union, Fset.singleton_spec; reflexivity. Qed.

Lemma err_has_attr : forall t, mem (err_attr O) (labels T (err_row O t)) = true.
Proof.
intro t; rewrite err_labels; replace (Oset.eq_bool (OAtt T) (err_attr O) (err_attr O)) with true;
  [apply orb_true_r | symmetry; apply eq_bool_err; reflexivity].
Qed.

Lemma srow_err : forall sa t, srow sa t -> srow sa (err_row O t).
Proof.
intros sa t H; right; split; [apply err_has_attr | ]; intros a Ha; rewrite err_labels in Ha.
apply orb_true_iff in Ha; destruct Ha as [Ha | Ha]; [ | right; apply eq_bool_err; exact Ha].
destruct H as [H | [_ H]]; [left; rewrite <- H; exact Ha | exact (H a Ha)].
Qed.

Lemma srow_null : forall sa, srow sa (null_tuple T sa).
Proof. intro sa; left; intro a; apply mem_labels_mk_tuple. Qed.

Lemma srow_mk : forall s f, srow s (mk_tuple T s f).
Proof. intros s f; left; intro a; apply mem_labels_mk_tuple. Qed.

Lemma srow_join : forall s1 s2 t1 t2, srow s1 t1 -> srow s2 t2 -> srow (s1 unionS s2) (join_tuple T t1 t2).
Proof.
intros s1 s2 t1 t2 H1 H2.
assert (L : forall a, mem a (labels T (join_tuple T t1 t2)) = mem a (labels T t1) || mem a (labels T t2))
  by (intro a; rewrite join_tuple_unfold, mem_labels_mk_tuple, Fset.mem_union; reflexivity).
assert (Sub : forall s t, srow s t -> forall a, mem a (labels T t) = true -> mem a s = true \/ a = err_attr O)
  by (intros s t [H | [_ H]] a Ha; [left; rewrite <- H; exact Ha | exact (H a Ha)]).
destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2].
- left; intro a; rewrite L, H1, H2, Fset.mem_union; reflexivity.
- right; split; [rewrite L, (proj1 H2); apply orb_true_r | ].
  intros a Ha; rewrite L in Ha; rewrite Fset.mem_union; apply orb_true_iff in Ha; destruct Ha as [Ha | Ha].
  + left; rewrite <- H1, Ha; reflexivity.
  + destruct ((proj2 H2) a Ha) as [K | K]; [left; rewrite K; apply orb_true_r | right; exact K].
- right; split; [rewrite L, (proj1 H1); reflexivity | ].
  intros a Ha; rewrite L in Ha; rewrite Fset.mem_union; apply orb_true_iff in Ha; destruct Ha as [Ha | Ha].
  + destruct ((proj2 H1) a Ha) as [K | K]; [left; rewrite K; reflexivity | right; exact K].
  + left; rewrite <- H2, Ha; apply orb_true_r.
- right; split; [rewrite L, (proj1 H1); reflexivity | ].
  intros a Ha; rewrite L in Ha; rewrite Fset.mem_union; apply orb_true_iff in Ha; destruct Ha as [Ha | Ha].
  + destruct ((proj2 H1) a Ha) as [K | K]; [left; rewrite K; reflexivity | right; exact K].
  + destruct ((proj2 H2) a Ha) as [K | K]; [left; rewrite K; apply orb_true_r | right; exact K].
Qed.

Lemma srow_extend : forall sa t a v, srow sa t -> srow (sa unionS Fset.singleton (A T) a) (extend_tuple O t a v).
Proof.
intros sa t a v H.
assert (L : forall b, mem b (labels T (extend_tuple O t a v)) = mem b (labels T t) || mem b (Fset.singleton (A T) a))
  by (intro b; unfold extend_tuple; rewrite mem_labels_mk_tuple, Fset.mem_union; reflexivity).
destruct H as [H | [H1 H2]].
- left; intro b; rewrite L, H, Fset.mem_union; reflexivity.
- right; split; [rewrite L, H1; reflexivity | ].
  intros b Hb; rewrite L in Hb; rewrite Fset.mem_union; apply orb_true_iff in Hb; destruct Hb as [Hb | Hb].
  + destruct (H2 b Hb) as [K | K]; [left; rewrite K; reflexivity | right; exact K].
  + left; rewrite Hb; apply orb_true_r.
Qed.

Lemma srow_mk_row : forall l, srow (Fset.mk_set (A T) (map (@fst _ _) l)) (mk_row O l).
Proof. intro l; apply srow_mk. Qed.

Lemma srow_rename : forall l t, srow (Fset.mk_set (A T) (map (@snd _ _) l)) (@SqlFull.rename_tuple T O (@Ren_List T l) t).
Proof. intros l t; apply srow_mk. Qed.

(** * Where the rows of the helpers of the evaluation come from *)

Lemma in_keep_errors : forall r all t, In t (keep_errors O r all) -> In t r \/ exists u, In u all /\ t = err_row O u.
Proof.
intros r all t; unfold keep_errors; destruct (existsb _ r); [left; exact H | ].
intro H; apply in_app_or in H; destruct H as [H | H]; [left; exact H | right].
apply in_map_iff in H; destruct H as [u [<- Hu]]; apply filter_In in Hu; exists u; split; [exact (proj1 Hu) | reflexivity].
Qed.

Lemma in_dedup_rec : forall (X : Type) (f : X -> tuple) seen l x, In x (dedup_rec O f seen l) -> In x l.
Proof.
intros X f seen l; revert seen; induction l as [ | y l IH]; intros seen x H; [exact H | ]; simpl in H.
destruct (tuple_mem O (f y) seen); [right; exact (IH _ _ H) | ].
destruct H as [<- | H]; [left; reflexivity | right; exact (IH _ _ H)].
Qed.

Lemma in_dedup_on : forall (X : Type) (f : X -> tuple) l x, In x (dedup_on O f l) -> In x l.
Proof. intros X f l x; rewrite dedup_on_rec; apply in_dedup_rec. Qed.

Lemma in_filter_occ : forall keep before l t, In t (filter_occ O keep before l) -> In t l.
Proof.
intros keep before l; revert before; induction l as [ | u l IH]; intros before t H; [exact H | ]; simpl in H.
apply in_app_or in H; destruct H as [H | H]; [ | right; exact (IH _ _ H)].
destruct (keep _ u); [destruct H as [<- | []]; left; reflexivity | destruct H].
Qed.

Lemma in_eval_set_op : forall o sq l1 l2 t, In t (eval_set_op O o sq l1 l2) -> In t l1 \/ In t l2.
Proof.
intros o sq l1 l2 t; unfold eval_set_op, dedup; destruct sq; destruct o; intro H;
  repeat match goal with
         | H : In _ (_ ++ _) |- _ => apply in_app_or in H; destruct H as [H | H]
         | H : In _ (filter _ _) |- _ => apply filter_In in H; destruct H as [H _]
         | H : In _ (dedup_on _ _ _) |- _ => apply in_dedup_on in H
         | H : In _ (filter_occ _ _ _ _) |- _ => apply in_filter_occ in H
         end; tauto.
Qed.

Lemma in_unify_rows : forall atts rows t, In t (unify_rows O atts rows) ->
  exists u, In u rows /\ forall a, mem a (labels T t) = mem a (labels T u).
Proof.
intros atts rows t H; unfold unify_rows in H; apply in_map_iff in H; destruct H as [[i u] [<- Hi]].
exists u; split; [exact (in_combine_r _ _ _ _ Hi) | intro a; apply mem_labels_mk_tuple].
Qed.

Lemma in_sort_on : forall (X : Type) specs (keys : X -> list (value T)) l x, In x (sort_on O specs keys l) -> In x l.
Proof.
intros X specs keys l x H; unfold sort_on, msort in H; apply in_map_iff in H; destruct H as [[k y] [<- Hy]].
apply in_msort_fuel in Hy; apply in_map_iff in Hy; destruct Hy as [z [E Hz]]; injection E; intros <- _; exact Hz.
Qed.

Lemma in_cross_product : forall l1 l2 t, In t (cross_product T l1 l2) ->
  exists t1 t2, In t1 l1 /\ In t2 l2 /\ t = join_tuple T t1 t2.
Proof.
intros l1 l2 t H; unfold cross_product in H; apply in_flat_map in H; destruct H as [t1 [H1 H]].
apply in_map_iff in H; destruct H as [t2 [<- H2]]; exists t1, t2; tauto.
Qed.

Lemma in_group_insert : forall (X : Type) k (y : X) gs g x, In g (map (@snd _ _) (group_insert O k y gs)) -> In x g ->
  x = y \/ exists g0, In g0 (map (@snd _ _) gs) /\ In x g0.
Proof.
intros X k y gs; induction gs as [ | [k' g'] gs IH]; intros g x Hg Hx; simpl in Hg.
- destruct Hg as [<- | []]; destruct Hx as [<- | []]; left; reflexivity.
- destruct (key_eqb O k k'); simpl in Hg; destruct Hg as [<- | Hg].
  + apply in_app_or in Hx; destruct Hx as [Hx | [<- | []]]; [right; exists g'; simpl; tauto | left; reflexivity].
  + right; exists g; simpl; tauto.
  + right; exists g'; simpl; tauto.
  + destruct (IH g x Hg Hx) as [K | [g0 [K1 K2]]]; [left; exact K | right; exists g0; simpl; tauto].
Qed.

Lemma in_group_on : forall (X : Type) (key : X -> list (value T)) l g x, In g (group_on O key l) -> In x g -> In x l.
Proof.
intros X key l g x; rewrite group_on_spec; unfold group_on_list.
assert (K : forall gs l, In g (map (@snd _ _) (fold_left (fun gs x => group_insert O (key x) x gs) l gs)) -> In x g ->
          In x l \/ exists g0, In g0 (map (@snd _ _) gs) /\ In x g0).
{ clear l; intros gs l; revert gs; induction l as [ | y l IH]; intros gs Hg Hx; [right; exists g; tauto | ].
  simpl in Hg; destruct (IH _ Hg Hx) as [H | [g0 [H1 H2]]]; [left; right; exact H | ].
  destruct (in_group_insert _ _ _ _ _ _ H1 H2) as [<- | H]; [left; left; reflexivity | right; exact H]. }
intros Hg Hx; destruct (K nil l Hg Hx) as [H | [g0 [[] _]]]; exact H.
Qed.

Lemma in_indexed_rec : forall (X : Type) i (l : list X) it, In it (indexed_rec i l) -> In (snd it) l.
Proof.
intros X i l; revert i; induction l as [ | y l IH]; intros i it H; [destruct H | ]; simpl in H.
destruct H as [<- | H]; [left; reflexivity | right; exact (IH _ _ H)].
Qed.

Lemma in_eval_window : forall part specs keys a w rows t, In t (eval_window O part specs keys a w rows) ->
  exists u v, In u rows /\ t = extend_tuple O u a v.
Proof.
intros part specs keys a w rows t H; unfold eval_window in H; apply in_flat_map in H; destruct H as [g [Hg H]].
apply in_map_iff in H; destruct H as [it [<- Hit]]; unfold indexed in Hit; apply in_indexed_rec in Hit.
apply in_sort_on in Hit; exists (snd it); eexists; split; [exact (in_group_on _ _ _ _ _ Hg Hit) | reflexivity].
Qed.

Lemma in_set_groupings : forall rv univ pos rows gh t,
  In gh (set_groupings (relname := relname) O rv univ pos rows) -> In t (fst gh) -> In t rows.
Proof.
intros rv univ pos rows gh t H Ht; unfold set_groupings in H; apply in_flat_map in H; destruct H as [p [_ H]].
apply in_map_iff in H; destruct H as [grp [<- Hg]]; simpl in Ht.
destruct p; [destruct Hg as [<- | []]; exact Ht | exact (in_group_on _ _ _ _ _ Hg Ht)].
Qed.

Lemma in_grouping_part : forall g gk rv imp rows gh t,
  In gh (grouping_part (relname := relname) O g gk rv imp rows) -> In t (fst gh) ->
  exists u, In u rows /\ (t = u \/ t = err_row O u).
Proof.
intros g gk rv imp rows gh t H Ht.
assert (K : In t (map (fun t => if existsb (is_error O) (gk t) then err_row O t else t) rows)).
{ unfold grouping_part in H; destruct g as [ | l | ss | l | l].
  - destruct imp; apply in_map_iff in H; destruct H as [grp [<- Hg]]; simpl in Ht.
    + destruct Hg as [<- | []]; exact Ht.
    + apply in_map_iff in Hg; destruct Hg as [u [<- Hu]]; destruct Ht as [<- | []]; exact Hu.
  - apply in_map_iff in H; destruct H as [grp [<- Hg]]; simpl in Ht; destruct l as [ | x l].
    + destruct Hg as [<- | []]; exact Ht.
    + exact (in_group_on _ _ _ _ _ Hg Ht).
  - exact (in_set_groupings _ _ _ _ _ _ H Ht).
  - exact (in_set_groupings _ _ _ _ _ _ H Ht).
  - exact (in_set_groupings _ _ _ _ _ _ H Ht). }
apply in_map_iff in K; destruct K as [u [E Hu]]; exists u; split; [exact Hu | ].
destruct (existsb _ (gk u)); [right | left]; symmetry; exact E.
Qed.

Lemma in_eval_join : forall jt s1 s2 l1 right l2 on mark t,
  In t (eval_join T jt s1 s2 l1 right l2 on mark) ->
  (exists t1 t2, In t1 l1 /\ In t2 (right t1) /\ t = mark (join_tuple T t1 t2)) \/
  (exists t1, In t1 l1 /\ t = join_tuple T t1 (null_tuple T s2)) \/
  (exists t2, In t2 l2 /\ t = join_tuple T (null_tuple T s1) t2).
Proof.
intros jt s1 s2 l1 right l2 on mark t H.
assert (M : forall t1, In t (map mark (filter on (map (join_tuple T t1) (right t1)))) -> In t1 l1 ->
          exists t1 t2, In t1 l1 /\ In t2 (right t1) /\ t = mark (join_tuple T t1 t2)).
{ intros t1 H1 I1; apply in_map_iff in H1; destruct H1 as [u [<- Hu]]; apply filter_In in Hu; destruct Hu as [Hu _].
  apply in_map_iff in Hu; destruct Hu as [t2 [<- H2]]; exists t1, t2; tauto. }
assert (Inner : In t (flat_map (fun t1 => map mark (filter on (map (join_tuple T t1) (right t1)))) l1) ->
          exists t1 t2, In t1 l1 /\ In t2 (right t1) /\ t = mark (join_tuple T t1 t2)).
{ intro K; apply in_flat_map in K; destruct K as [t1 [I1 K]]; exact (M t1 K I1). }
assert (Left : In t (flat_map (fun t1 => match map mark (filter on (map (join_tuple T t1) (right t1))) with
                                         | nil => join_tuple T t1 (null_tuple T s2) :: nil
                                         | l => l end) l1) ->
          (exists t1 t2, In t1 l1 /\ In t2 (right t1) /\ t = mark (join_tuple T t1 t2)) \/
          (exists t1, In t1 l1 /\ t = join_tuple T t1 (null_tuple T s2))).
{ intro K; apply in_flat_map in K; destruct K as [t1 [I1 K]].
  destruct (map mark (filter on (map (join_tuple T t1) (right t1)))) as [ | x l] eqn:E.
  - destruct K as [<- | []]; right; exists t1; tauto.
  - left; rewrite <- E in K; exact (M t1 K I1). }
assert (Pad : In t (map (fun t2 => join_tuple T (null_tuple T s1) t2)
                        (filter (fun t2 => negb (existsb (fun t1 => on (join_tuple T t1 t2)) l1)) l2)) ->
          exists t2, In t2 l2 /\ t = join_tuple T (null_tuple T s1) t2).
{ intro K; apply in_map_iff in K; destruct K as [t2 [<- K]]; apply filter_In in K; exists t2; tauto. }
unfold eval_join in H; destruct jt; try (apply in_app_or in H; destruct H as [H | H]).
- left; exact (Inner H).
- destruct (Left H) as [K | K]; [left | right; left]; exact K.
- left; exact (Inner H).
- right; right; exact (Pad H).
- destruct (Left H) as [K | K]; [left | right; left]; exact K.
- right; right; exact (Pad H).
Qed.

Lemma rec_loop_inv : forall (P : tuple -> Prop) step d sa,
  P (err_row O (null_tuple T sa)) ->
  (forall w, (forall t, In t w -> P t) -> forall t, In t (step w) -> P t) ->
  forall n acc work, (forall t, In t acc -> P t) -> (forall t, In t work -> P t) ->
  forall t, In t (rec_loop O step d sa n acc work) -> P t.
Proof.
intros P step d sa He Hs n; induction n as [ | n IH]; intros acc work Ha Hw t H; simpl in H.
- destruct work; [exact (Ha t H) | ]; apply in_app_or in H; destruct H as [H | [<- | []]]; [exact (Ha t H) | exact He].
- destruct work as [ | w0 work]; [exact (Ha t H) | ].
  assert (N : forall t, In t (if d then eval_set_op O Diff Set_Distinct (step (w0 :: work)) acc else step (w0 :: work)) -> P t).
  { intros u Hu; destruct d; [apply in_eval_set_op in Hu; destruct Hu as [Hu | Hu] | ];
      [exact (Hs _ Hw u Hu) | exact (Ha u Hu) | exact (Hs _ Hw u Hu)]. }
  apply (IH _ _ (fun u Hu => match in_app_or _ _ _ Hu with or_introl K => Ha u K | or_intror K => N u K end) N t H).
Qed.

(** * The conditions of the theorem *)

Notation squery := (squery T relname).
Notation sspec := (sspec T relname).
Notation sfrom := (sfrom T relname).
Notation ssort := (squery_sort ORN basesort).
Notation psort := (sspec_sort ORN basesort).
Notation fsort := (sfrom_sort ORN basesort).

(** the recursive term of a [WITH RECURSIVE] has the sort of the base (through the [FROM] clauses: the
    subqueries of the expressions do not give rows to the result) *)
Fixpoint rok_q (ce : cte_env T relname) (q : squery) {struct q} : bool :=
  match q with
  | SQ_Table _ _ => true
  | SQ_Set _ _ q1 q2 => rok_q ce q1 && rok_q ce q2
  | SQ_Select sp => rok_s ce sp
  | SQ_Order q _ _ _ | SQ_Fetch q _ _ _ _ _ | SQ_Window q _ => rok_q ce q
  | SQ_With r q1 q2 => rok_q ce q1 && rok_q ((r, (ssort ce q1, nil)) :: ce) q2
  | SQ_WithRec _ r q1 q2 q3 =>
    let ce' := (r, (ssort ce q1, nil)) :: ce in
    rok_q ce q1 && rok_q ce' q2 && rok_q ce' q3 && Fset.equal (A T) (ssort ce' q2) (ssort ce q1)
  end
with rok_s (ce : cte_env T relname) (sp : sspec) {struct sp} : bool :=
  match sp with Select _ _ lf _ _ _ => forallb (rok_f ce) lf end
with rok_f (ce : cte_env T relname) (f : sfrom) {struct f} : bool :=
  match f with
  | Fr_Query q _ => rok_q ce q
  | Fr_Join _ _ f1 f2 _ => rok_f ce f1 && rok_f ce f2
  | Fr_Fun _ _ _ _ => true
  end.

(** the rows of the stored relations and of the [WITH] relations have their sorts *)
Definition inst_ok := forall r t, In t (Febag.elements BTupleT (instance r)) -> srow (basesort r) t.

Definition ce_ok (ce : cte_env T relname) :=
  forall r sa l, Oset.find ORN r ce = Some (sa, l) -> forall t, In t l -> srow sa t.

Definition same_sorts (ce1 ce2 : cte_env T relname) :=
  forall r, option_map (@fst _ _) (Oset.find ORN r ce1) = option_map (@fst _ _) (Oset.find ORN r ce2).

Lemma same_sorts_cons : forall r s x y ce1 ce2, same_sorts ce1 ce2 ->
  same_sorts ((r, (s, x)) :: ce1) ((r, (s, y)) :: ce2).
Proof.
intros r s x y ce1 ce2 H r0; unfold Oset.find; cbn [Mem.find].
destruct (Oset.eq_bool ORN r0 r); [reflexivity | apply H].
Qed.

Lemma same_sorts_refl : forall ce, same_sorts ce ce.
Proof. intros ce r; reflexivity. Qed.

(** the sorts, and the condition [rok], read only the sorts of the [WITH] relations *)
Lemma sorts_same : forall q ce1 ce2, same_sorts ce1 ce2 -> ssort ce1 q = ssort ce2 q /\ rok_q ce1 q = rok_q ce2 q.
Proof.
apply (ind_q T relname (fun _ => True) (fun _ => True)
  (fun q => forall ce1 ce2, same_sorts ce1 ce2 -> ssort ce1 q = ssort ce2 q /\ rok_q ce1 q = rok_q ce2 q)
  (fun sp => forall ce1 ce2, same_sorts ce1 ce2 -> psort ce1 sp = psort ce2 sp /\ rok_s ce1 sp = rok_s ce2 sp)
  (fun f => forall ce1 ce2, same_sorts ce1 ce2 -> fsort ce1 f = fsort ce2 f /\ rok_f ce1 f = rok_f ce2 f));
  unfold LE, LO; intros; try exact I.
- cbn [squery_sort rok_q]; split; [ | reflexivity].
  generalize (H r); destruct (Oset.find ORN r ce1) as [[s1 l1] | ]; destruct (Oset.find ORN r ce2) as [[s2 l2] | ];
    simpl; intro E; try discriminate; [injection E; intros; assumption | reflexivity].
- cbn [squery_sort rok_q]; destruct (H ce1 ce2 H1) as [E1 R1]; destruct (H0 ce1 ce2 H1) as [E2 R2].
  rewrite E1, R1, R2; split; reflexivity.
- cbn [squery_sort rok_q]; exact (H ce1 ce2 H0).
- cbn [squery_sort rok_q]; destruct (H ce1 ce2 H2) as [E1 R1]; rewrite E1, R1; split; reflexivity.
- cbn [squery_sort rok_q]; destruct (H ce1 ce2 H2) as [E1 R1]; rewrite E1, R1; split; reflexivity.
- cbn [squery_sort rok_q]; destruct (H ce1 ce2 H1) as [E1 R1]; rewrite E1, R1; split; reflexivity.
- cbn [squery_sort rok_q]; destruct (H ce1 ce2 H1) as [E1 R1].
  destruct (H0 _ _ (same_sorts_cons r (ssort ce1 q1) nil nil ce1 ce2 H1)) as [E2 R2].
  rewrite E2, R2, R1, E1; split; reflexivity.
- cbn [squery_sort rok_q]; destruct (H ce1 ce2 H2) as [E1 R1].
  destruct (H0 _ _ (same_sorts_cons r (ssort ce1 q1) nil nil ce1 ce2 H2)) as [E2 R2].
  destruct (H1 _ _ (same_sorts_cons r (ssort ce1 q1) nil nil ce1 ce2 H2)) as [E3 R3].
  cbv zeta; rewrite E2, E3, R2, R3, R1, E1; split; reflexivity.
- cbn [sspec_sort rok_s]; split.
  + destruct s; [ | reflexivity]; f_equal; apply map_ext_in; intros f Hf; exact (proj1 (H0 f Hf ce1 ce2 H4)).
  + clear H; induction lf as [ | f lf IH]; [reflexivity | ]; simpl.
    rewrite (proj2 (H0 f (or_introl eq_refl) ce1 ce2 H4)), IH; [reflexivity | ].
    intros f' Hf'; apply H0; right; exact Hf'.
- destruct (H ce1 ce2 H0) as [E1 R1]; destruct rho; cbn [sfrom_sort rok_f]; fold (@squery_sort T relname ORN basesort) rok_q; rewrite R1; [rewrite E1 | ]; split; reflexivity.
- cbn [sfrom_sort rok_f]; destruct (H ce1 ce2 H2) as [E1 R1]; destruct (H0 ce1 ce2 H2) as [E2 R2].
  rewrite E1, E2, R1, R2; split; reflexivity.
- split; reflexivity.
Qed.

(** * More facts on rows *)

Lemma srow_labels : forall s t u, (forall a, mem a (labels T t) = mem a (labels T u)) -> srow s u -> srow s t.
Proof.
intros s t u E [H | [H1 H2]]; [left; intro a; rewrite E; apply H | right; split; [rewrite E; exact H1 | ]].
intros a Ha; rewrite E in Ha; exact (H2 a Ha).
Qed.

Lemma srow_union_l : forall s1 s2 t, mem (err_attr O) (labels T t) = true -> srow s1 t -> srow (s1 unionS s2) t.
Proof. intros s1 s2 t He H; apply (srow_sub s1); [intros a Ha; rewrite Fset.mem_union, Ha; reflexivity | exact He | exact H]. Qed.

Lemma srow_union_r : forall s1 s2 t, mem (err_attr O) (labels T t) = true -> srow s2 t -> srow (s1 unionS s2) t.
Proof. intros s1 s2 t He H; apply (srow_sub s2); [intros a Ha; rewrite Fset.mem_union, Ha; apply orb_true_r | exact He | exact H]. Qed.

Lemma srow_keep : forall s r all t, (forall u, In u r -> srow s u) -> (forall u, In u all -> srow s u) ->
  In t (keep_errors O r all) -> srow s t.
Proof.
intros s r all t Hr Ha H; destruct (in_keep_errors _ _ _ H) as [K | [u [Hu ->]]]; [exact (Hr t K) | ].
apply srow_err, Ha, Hu.
Qed.

Lemma ce_ok_cons : forall ce r sa l, ce_ok ce -> (forall t, In t l -> srow sa t) -> ce_ok ((r, (sa, l)) :: ce).
Proof.
intros ce r sa l H Hl r0 sa0 l0 E t Ht; unfold Oset.find in E; cbn [Mem.find] in E.
destruct (Oset.eq_bool ORN r0 r); [injection E; intros <- <-; exact (Hl t Ht) | exact (H r0 sa0 l0 E t Ht)].
Qed.

(** * The theorem *)

Hypothesis Hinst : inst_ok.

Notation eq_ := (eval_squery ORN O basesort instance).
Notation es_ := (eval_sspec ORN O basesort instance).
Notation ef_ := (eval_sfrom ORN O basesort instance).

Definition Qs (q : squery) := forall ce env, ce_ok ce -> rok_q ce q = true ->
  forall t, In t (eq_ ce env q) -> srow (ssort ce q) t.
Definition Ss (sp : sspec) := forall ce env ex, ce_ok ce -> rok_s ce sp = true ->
  forall x, In x (es_ ce env sp ex) -> srow (psort ce sp) (fst x).
Definition Fs (f : sfrom) := forall ce env, ce_ok ce -> rok_f ce f = true ->
  forall t, In t (ef_ ce env f) -> srow (fsort ce f) t.
Definition Tr {X : Type} (_ : X) := True.

Ltac unf := cbn [eval_squery eval_sspec eval_sfrom squery_sort sspec_sort sfrom_sort rok_q rok_s rok_f];
  fold (eval_sexpr ORN O basesort instance) (eval_scond ORN O basesort instance)
       (scond_raises ORN O basesort instance) eq_ es_ ef_
       (@squery_sort T relname ORN basesort) (@sspec_sort T relname ORN basesort) (@sfrom_sort T relname ORN basesort)
       rok_q rok_s rok_f.

Lemma s_table : forall r, Qs (SQ_Table T r).
Proof.
intros r ce env Hce _ t; unf.
destruct (Oset.find ORN r ce) as [[sa l] | ] eqn:E; [exact (Hce r sa l E t) | apply Hinst].
Qed.

Lemma s_set : forall o sq q1 q2, Qs q1 -> Qs q2 -> Qs (SQ_Set o sq q1 q2).
Proof.
intros o sq q1 q2 H1 H2 ce env Hce R t; unf; apply andb_true_iff in R; destruct R as [R1 R2].
destruct (Fset.equal (A T) (ssort ce q1) (ssort ce q2)) eqn:E; [ | intros []].
intro Ht; destruct (in_unify_rows _ _ _ Ht) as [u [Hu L]]; apply (srow_labels _ _ _ L).
assert (K : forall v, In v (eq_ ce env q1 ++ eq_ ce env q2) -> srow (ssort ce q1) v).
{ intros v Hv; apply in_app_or in Hv; destruct Hv as [Hv | Hv]; [exact (H1 ce env Hce R1 v Hv) | ].
  apply (srow_eq (ssort ce q2)); [ | exact (H2 ce env Hce R2 v Hv)].
  intro a; rewrite Fset.equal_spec in E; symmetry; apply E. }
apply (srow_keep _ _ _ _ (fun v Hv => K v (match in_eval_set_op _ _ _ _ _ Hv with
                                             | or_introl h => in_or_app _ _ _ (or_introl h)
                                             | or_intror h => in_or_app _ _ _ (or_intror h) end)) K Hu).
Qed.

Lemma s_select : forall sp, Ss sp -> Qs (SQ_Select sp).
Proof.
intros sp H ce env Hce R t; unf; intro Ht; apply in_map_iff in Ht; destruct Ht as [x [<- Hx]].
exact (H ce env nil Hce R x Hx).
Qed.

Lemma ord_rows_sorts : forall q lo ce env, ce_ok ce -> rok_q ce q = true -> Qs q -> (forall sp, q = SQ_Select sp -> Ss sp) ->
  forall x, In x (match q with
                  | SQ_Select sp => es_ ce env sp (map (fun o => match o with O_By e _ _ => e end) lo)
                  | _ => map (fun t => (t, slice_t T relname t :: env)) (eq_ ce env q)
                  end) -> srow (ssort ce q) (fst x).
Proof.
intros q lo ce env Hce R Hq Hs x Hx.
assert (M : In x (map (fun t => (t, slice_t T relname t :: env)) (eq_ ce env q)) -> srow (ssort ce q) (fst x))
  by (intro K; apply in_map_iff in K; destruct K as [t [<- Ht]]; exact (Hq ce env Hce R t Ht)).
destruct q; try exact (M Hx).
exact (Hs s eq_refl ce env _ Hce R x Hx).
Qed.

Lemma flag_sorts : forall (keys : tuple * senv T relname -> list (value T)) rows s,
  (forall x, In x rows -> srow s (fst x)) ->
  forall x, In x (map (fun x => if existsb (is_error O) (keys x) then (err_row O (fst x), snd x) else x) rows) ->
  srow s (fst x).
Proof.
intros keys rows s H x Hx; apply in_map_iff in Hx; destruct Hx as [y [<- Hy]].
destruct (existsb _ (keys y)); [apply srow_err | ]; exact (H y Hy).
Qed.

Lemma s_order : forall q lo off lim, Qs q -> (forall sp, q = SQ_Select sp -> Ss sp) -> LO T relname Tr lo ->
  Qs (SQ_Order q lo off lim).
Proof.
intros q lo off lim Hq Hs _ ce env Hce R t; unf; cbv zeta.
apply srow_keep.
- intros u Hu; apply in_map_iff in Hu; destruct Hu as [x [<- Hx]].
  apply in_offset_limit, in_sort_on in Hx; revert x Hx; apply flag_sorts; apply ord_rows_sorts; assumption.
- intros u Hu; apply in_map_iff in Hu; destruct Hu as [x [<- Hx]]; revert x Hx; apply flag_sorts;
    apply ord_rows_sorts; assumption.
Qed.

Lemma in_take : forall (X : Type) (f : X -> comparison) l x,
  In x ((fix take (l : list X) : list X :=
           match l with
           | y :: l' => match f y with Eq => y :: take l' | _ => nil end
           | nil => nil
           end) l) -> In x l.
Proof.
intros X f l x; induction l as [ | y l IH]; [intro H; exact H | ]; simpl; destruct (f y); simpl; try tauto.
Qed.

Lemma s_fetch : forall q lo off ties pct n, Qs q -> (forall sp, q = SQ_Select sp -> Ss sp) -> LO T relname Tr lo ->
  Qs (SQ_Fetch q lo off ties pct n).
Proof.
intros q lo off ties pct n Hq Hs _ ce env Hce R t; unf; cbv zeta.
match goal with |- In t (keep_errors O (map _ (?F ++ ?E)) (map _ ?RS)) -> _ =>
  assert (HR : forall x, In x RS -> srow (ssort ce q) (fst x)) by (apply flag_sorts; apply ord_rows_sorts; assumption);
  set (rows := RS) in *; set (first := F) in *; set (extra := E) in * end.
apply srow_keep; [ | intros u Hu; apply in_map_iff in Hu; destruct Hu as [x [<- Hx]]; exact (HR x Hx)].
intros u Hu; apply in_map_iff in Hu; destruct Hu as [x [<- Hx]]; apply HR.
apply in_app_or in Hx; destruct Hx as [Hx | Hx].
- unfold first in Hx; apply In_firstn in Hx; destruct off as [k | ]; [apply In_skipn in Hx | ]; apply in_sort_on in Hx; exact Hx.
- unfold extra in Hx; destruct ties; [ | simpl in Hx; destruct Hx].
  match goal with H : In _ (match rev' ?F with _ => _ end) |- _ => destruct (rev' F) as [ | last l] end; [simpl in Hx; destruct Hx | ].
  apply in_take in Hx; apply In_skipn in Hx; destruct off as [k | ]; [apply In_skipn in Hx | ]; apply in_sort_on in Hx; exact Hx.
Qed.

Lemma fold_windows : forall (F : swindow T relname -> list tuple -> list tuple),
  (forall w s rows, (forall t, In t rows -> srow s t) -> forall t, In t (F w rows) ->
                    srow (s unionS Fset.singleton (A T) (swindow_att w)) t) ->
  forall lw s rows, (forall t, In t rows -> srow s t) ->
  forall t, In t (fold_left (fun rows w => w rows) (map F lw) rows) ->
            srow (s unionS Fset.mk_set (A T) (map (@swindow_att _ _) lw)) t.
Proof.
intros F HF lw; induction lw as [ | w lw IH]; intros s rows Hr t Ht; simpl in Ht.
- apply (srow_eq s); [intro a; rewrite Fset.mem_union, Fset.mem_mk_set; simpl; rewrite orb_false_r; reflexivity | ].
  exact (Hr t Ht).
- apply (srow_eq ((s unionS Fset.singleton (A T) (swindow_att w)) unionS Fset.mk_set (A T) (map (@swindow_att _ _) lw))).
  + intro a; rewrite !Fset.mem_union, !Fset.mem_mk_set, Fset.singleton_spec; simpl.
    destruct (mem a s); destruct (Oset.eq_bool (OAtt T) a (swindow_att w));
      destruct (Oset.mem_bool (OAtt T) a (map (@swindow_att _ _) lw)); reflexivity.
  + exact (IH _ _ (HF w s rows Hr) t Ht).
Qed.

Lemma s_window : forall q lw, Qs q ->
  (forall f lp lo a, In (W_As f lp lo a) lw -> LE T relname Tr lp /\ LO T relname Tr lo /\ LE T relname Tr (wexprs T relname f)) ->
  Qs (SQ_Window q lw).
Proof.
intros q lw Hq _ ce env Hce R t; unf; intro Ht.
refine (fold_windows _ _ lw (ssort ce q) _ (Hq ce env Hce R) t Ht).
intros [f lp lo a] s0 rows Hr u Hu; cbv beta iota in Hu.
destruct (in_eval_window _ _ _ _ _ _ _ Hu) as [v [x [Hv ->]]].
apply srow_extend; apply in_map_iff in Hv; destruct Hv as [y [<- Hy]].
destruct (existsb _ _); [apply srow_err | ]; exact (Hr y Hy).
Qed.

Lemma s_with : forall r q1 q2, Qs q1 -> Qs q2 -> Qs (SQ_With r q1 q2).
Proof.
intros r q1 q2 H1 H2 ce env Hce R t; unf.
change (rok_q ce q1 && rok_q ((r, (ssort ce q1, nil)) :: ce) q2 = true) in R.
apply andb_true_iff in R; destruct R as [R1 R2].
assert (S := sorts_same q2 _ ((r, (ssort ce q1, eq_ ce env q1)) :: ce)
               (same_sorts_cons r (ssort ce q1) nil (eq_ ce env q1) ce ce (same_sorts_refl ce))).
rewrite (proj1 S); rewrite (proj2 S) in R2; apply H2; [ | exact R2].
apply ce_ok_cons; [exact Hce | exact (H1 ce env Hce R1)].
Qed.

Lemma s_withrec : forall sq r q1 q2 q3, Qs q1 -> Qs q2 -> Qs q3 -> Qs (SQ_WithRec sq r q1 q2 q3).
Proof.
intros sq r q1 q2 q3 H1 H2 H3 ce env Hce R; unf; cbv zeta in *.
change (rok_q ce q1 && rok_q ((r, (ssort ce q1, nil)) :: ce) q2 && rok_q ((r, (ssort ce q1, nil)) :: ce) q3 &&
        Fset.equal (A T) (ssort ((r, (ssort ce q1, nil)) :: ce) q2) (ssort ce q1) = true) in R.
rewrite !andb_true_iff in R; destruct R as [[[R1 R2] R3] E].
set (sa := ssort ce q1) in *.
assert (Base : forall t, In t (if is_distinct sq then eval_set_op O Union Set_Distinct (eq_ ce env q1) nil else eq_ ce env q1) ->
          srow sa t).
{ intros t Ht; destruct (is_distinct sq); [apply in_eval_set_op in Ht; destruct Ht as [Ht | []] | ];
    exact (H1 ce env Hce R1 t Ht). }
assert (Res : forall t, In t (rec_loop O (fun work => eq_ ((r, (sa, work)) :: ce) env q2) (is_distinct sq) sa rec_fuel
                              (if is_distinct sq then eval_set_op O Union Set_Distinct (eq_ ce env q1) nil else eq_ ce env q1)
                              (if is_distinct sq then eval_set_op O Union Set_Distinct (eq_ ce env q1) nil else eq_ ce env q1)) ->
          srow sa t).
{ apply rec_loop_inv; [apply srow_err, srow_null | | exact Base | exact Base].
  intros w Hw t Ht.
  assert (S := sorts_same q2 _ ((r, (sa, w)) :: ce) (same_sorts_cons r sa nil w ce ce (same_sorts_refl ce))).
  apply (srow_eq (ssort ((r, (sa, w)) :: ce) q2)).
  - rewrite <- (proj1 S); intro a; rewrite Fset.equal_spec in E; apply E.
  - apply (H2 _ env (ce_ok_cons _ _ _ _ Hce Hw)); [rewrite <- (proj2 S); exact R2 | exact Ht]. }
intros t Ht.
match type of Ht with In t (eq_ ((r, (sa, ?RES)) :: ce) env q3) =>
  assert (S := sorts_same q3 _ ((r, (sa, RES)) :: ce) (same_sorts_cons r sa nil RES ce ce (same_sorts_refl ce)));
  rewrite (proj1 S); apply (H3 _ env (ce_ok_cons _ _ _ _ Hce Res)); [rewrite <- (proj2 S); exact R3 | exact Ht] end.
Qed.

Lemma from_sorts : forall ce env lf, (forall f, In f lf -> forall t, In t (ef_ ce env f) -> srow (fsort ce f) t) ->
  forall acc S, (forall t, In t acc -> srow S t) ->
  forall t, In t (fold_left (fun l1 l2 => keep_errors O (cross_product T l1 l2) (l1 ++ l2)) (map (ef_ ce env) lf) acc) ->
            srow (S unionS Fset.Union (A T) (map (fsort ce) lf)) t.
Proof.
intros ce env lf; induction lf as [ | f lf IH]; intros Hf acc S Ha t Ht; simpl in Ht.
- apply (srow_eq S); [intro a; rewrite Fset.mem_union, Fset.Union_unfold, Fset.empty_spec, orb_false_r; reflexivity | ].
  exact (Ha t Ht).
- apply (srow_eq ((S unionS fsort ce f) unionS Fset.Union (A T) (map (fsort ce) lf))).
  + intro a; change (map (fsort ce) (f :: lf)) with (fsort ce f :: map (fsort ce) lf).
    rewrite (Fset.Union_unfold _ (fsort ce f :: map (fsort ce) lf)), !Fset.mem_union.
    destruct (mem a S); destruct (mem a (fsort ce f)); reflexivity.
  + refine (IH (fun f' Hf' => Hf f' (or_intror Hf')) _ _ _ t Ht).
    intros u Hu; destruct (in_keep_errors _ _ _ Hu) as [K | [v [Hv ->]]].
    * destruct (in_cross_product _ _ _ K) as [t1 [t2 [H1 [H2 ->]]]].
      apply srow_join; [exact (Ha t1 H1) | exact (Hf f (or_introl eq_refl) t2 H2)].
    * apply in_app_or in Hv; destruct Hv as [Hv | Hv];
        [apply srow_union_l | apply srow_union_r]; try apply err_has_attr; apply srow_err;
        [exact (Ha v Hv) | exact (Hf f (or_introl eq_refl) v Hv)].
Qed.

Lemma srow_empty : srow (Fset.empty (A T)) (empty_tuple T).
Proof. left; intro a; apply Fset.mem_eq_2; apply labels_empty_tuple. Qed.

Lemma s_spec : forall sq s lf w g h,
  match s with S_Star _ _ => True | S_List l => forall e a, In (S_As e a) l -> Tr e end ->
  (forall f, In f lf -> Fs f) -> Tr w ->
  match g with
  | G_Fine _ _ => True
  | G_By l | G_Rollup l | G_Cube l => LE T relname Tr l
  | G_Sets ss => forall l, In l ss -> LE T relname Tr l
  end -> Tr h -> Ss (Select sq s lf w g h).
Proof.
intros sq s lf w g h _ Hf _ _ _ ce env ex Hce R x Hx.
change (forallb (rok_f ce) lf = true) in R; rewrite forallb_forall in R.
rewrite eval_select in Hx; cbv zeta in Hx.
set (sa := Fset.Union (A T) (map (fsort ce) lf)) in *.
(* the rows of the FROM and WHERE clauses *)
assert (W : forall t, In t (where_rows ORN O basesort instance ce env lf w) -> srow sa t).
{ intros t Ht; unfold where_rows in Ht; apply in_flat_map in Ht; destruct Ht as [u [Hu Ht]].
  assert (Su : srow sa u).
  { apply (srow_eq (Fset.empty (A T) unionS sa));
      [intro a; rewrite Fset.mem_union, Fset.empty_spec; reflexivity | ].
    refine (from_sorts ce env lf (fun f Hf' => Hf f Hf' ce env Hce (R f Hf')) _ _ _ u Hu).
    intros v [<- | []]; exact srow_empty. }
  destruct (_ || _); [destruct Ht as [<- | []]; apply srow_err; exact Su | ].
  destruct (is_true3 _ _); [destruct Ht as [<- | []]; exact Su | destruct Ht]. }
assert (G : forall gh, In gh (grouping_part O g (gkeys_of ORN O basesort instance ce env g)
                                (row_vals_of ORN O basesort instance ce env g)
                                (implicit_group ORN basesort ce sa s h ex) (where_rows ORN O basesort instance ce env lf w)) ->
            forall t, In t (fst gh) -> srow sa t).
{ intros gh Hgh t Ht; destruct (in_grouping_part _ _ _ _ _ _ _ Hgh Ht) as [u [Hu [-> | ->]]];
    [ | apply srow_err]; exact (W u Hu). }
revert G Hx; generalize (grouping_part O g (gkeys_of ORN O basesort instance ce env g)
                        (row_vals_of ORN O basesort instance ce env g)
                        (implicit_group ORN basesort ce sa s h ex) (where_rows ORN O basesort instance ce env lf w)).
intros gs G Hx; unfold select_rest in Hx; cbv zeta in Hx.
assert (D : forall (l : list (tuple * senv T relname)), In x (match sq with Set_All => l | Set_Distinct => dedup_on O (@fst _ _) l end) -> In x l)
  by (intros l Hl; destruct sq; [exact Hl | exact (in_dedup_on _ _ _ _ Hl)]).
apply D in Hx; clear D; apply in_map_iff in Hx; destruct Hx as [y [<- Hy]].
apply filter_In in Hy; destruct Hy as [Hy _]; apply in_map_iff in Hy; destruct Hy as [ge [<- Hge]].
apply in_map_iff in Hge; destruct Hge as [gh [<- Hgh]]; simpl.
match goal with |- srow _ (if ?b then _ else _) => destruct b; [apply srow_err | ] end.
all: destruct s as [ | l]; cbn [sspec_sort].
1, 3: destruct (fst gh) as [ | t g'] eqn:E; [apply srow_null | ]; apply (G gh Hgh); rewrite E; left; reflexivity.
all: match goal with |- srow _ (mk_row O ?L) =>
       apply (srow_eq (Fset.mk_set (A T) (map (@fst _ _) L))); [ | apply srow_mk_row] end.
all: intro a; rewrite !Fset.mem_mk_set, map_map; f_equal; apply map_ext; intros [e a']; reflexivity.
Qed.

Lemma s_fquery : forall q rho, Qs q -> Fs (Fr_Query q rho).
Proof.
intros q rho Hq ce env Hce R t; change (rok_q ce q = true) in R; unf; intro Ht.
apply in_map_iff in Ht; destruct Ht as [u [<- Hu]]; cbv zeta.
destruct rho as [ | l]; cbn [sfrom_sort]; fold (@squery_sort T relname ORN basesort).
- cbn [SqlFull.rename_tuple]; destruct (_ && _); [apply srow_err | ]; exact (Hq ce env Hce R u Hu).
- destruct (_ && _); [apply srow_err | ]; apply srow_rename.
Qed.

Lemma s_fjoin : forall jt lat f1 f2 c, Fs f1 -> Fs f2 -> Tr c -> Fs (Fr_Join jt lat f1 f2 c).
Proof.
intros jt lat f1 f2 c H1 H2 _ ce env Hce R t; change (rok_f ce f1 && rok_f ce f2 = true) in R.
apply andb_true_iff in R; destruct R as [R1 R2]; unf; cbv zeta; intro Ht.
assert (J : forall on mark, (forall u, mark u = u \/ mark u = err_row O u) ->
          forall u, In u (eval_join T jt (fsort ce f1) (fsort ce f2) (ef_ ce env f1)
                             (fun t1 => if lat then ef_ ce (slice_t T relname t1 :: env) f2 else ef_ ce env f2)
                             (ef_ ce env f2) on mark) -> srow (fsort ce f1 unionS fsort ce f2) u).
{ intros on mark Hm u Hu;
    destruct (in_eval_join _ _ _ _ _ _ _ _ _ Hu) as [[t1 [t2 [K1 [K2 ->]]]] | [[t1 [K1 ->]] | [t2 [K2 ->]]]].
  - assert (S2 : srow (fsort ce f2) t2) by (destruct lat; [exact (H2 _ _ Hce R2 t2 K2) | exact (H2 _ _ Hce R2 t2 K2)]).
    destruct (Hm (join_tuple T t1 t2)) as [E | E]; rewrite E; [ | apply srow_err];
      apply srow_join; trivial; exact (H1 _ _ Hce R1 t1 K1).
  - apply srow_join; [exact (H1 _ _ Hce R1 t1 K1) | apply srow_null].
  - apply srow_join; [apply srow_null | exact (H2 _ _ Hce R2 t2 K2)]. }
assert (Hm : forall bad : tuple -> bool, forall u, (if bad u then err_row O u else u) = u \/
                                                 (if bad u then err_row O u else u) = err_row O u)
  by (intros bad u; destruct (bad u); [right | left]; reflexivity).
match type of Ht with In t (if ?b then _ else _) => destruct b end; [ | exact (J _ _ (Hm _) t Ht)].
destruct (in_keep_errors _ _ _ Ht) as [K | [v [Hv ->]]]; [exact (J _ _ (Hm _) t K) | ].
apply in_app_or in Hv; destruct Hv as [Hv | Hv]; [apply srow_union_l | apply srow_union_r]; try apply err_has_attr;
  apply srow_err; [exact (H1 _ _ Hce R1 v Hv) | exact (H2 _ _ Hce R2 v Hv)].
Qed.

Lemma s_ffun : forall name args ord atts, LE T relname Tr args -> Fs (Fr_Fun name args ord atts).
Proof.
intros name args ord atts _ ce env Hce R t; unf; cbv zeta; intro Ht.
destruct (first_error O _); [destruct Ht as [<- | []]; apply srow_err, srow_mk | ].
destruct (table_fun O name); [ | destruct Ht as [<- | []]; apply srow_err, srow_mk].
apply in_map_iff in Ht; destruct Ht as [[i0 l0] [<- _]]; apply srow_mk.
Qed.

Theorem eval_sorts : forall q ce env, ce_ok ce -> rok_q ce q = true ->
  forall t, In t (eval_squery ORN O basesort instance ce env q) -> srow (squery_sort ORN basesort ce q) t.
Proof.
intro q; apply (ind_q T relname Tr Tr Qs Ss Fs); intros; try exact I.
- apply s_table.
- apply s_set; assumption.
- apply s_select; assumption.
- apply s_order; assumption.
- apply s_fetch; assumption.
- apply s_window; assumption.
- apply s_with; assumption.
- apply s_withrec; assumption.
- apply s_spec; assumption.
- apply s_fquery; assumption.
- apply s_fjoin; assumption.
- apply s_ffun; assumption.
Qed.

Lemma ce_ok_nil : ce_ok nil.
Proof. intros r sa l E; discriminate E. Qed.

(** the rows of a query of the database *)
Corollary query_sorts : forall q, rok_q nil q = true ->
  forall t, In t (eval_query_list ORN O basesort instance q) -> srow (sort_of_query ORN basesort q) t.
Proof. intros q R t Ht; exact (eval_sorts q nil nil ce_ok_nil R t Ht). Qed.

End Sec.
