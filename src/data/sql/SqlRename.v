(** * Renaming the attributes (TODO 6.3, issue I4)

    The evaluation of [SqlFull.v] does not depend on the names of the attributes: for a bijection [rho] of
    the attributes which preserves their order, their types and their affinities, and fixes the attribute of
    the failed rows, the rows of the renamed query over the renamed database are the renamed rows of the query
    ([eval_rename]). The front end names the columns of each item of a [FROM] clause and of each derived table
    by their positions, so that the named semantics of [SqlFull.v] is a positional semantics in which two
    columns never share a name; this theorem says that the choice of the names does not matter. *)
Require Import List Bool Sorting.
Require Import BasicFacts ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection FlatData SqlFull.
Import Tuple.

Section Tuples.

Hypothesis T : Tuple.Rcd.
Hypothesis rho : attribute T -> attribute T.
Hypothesis rhoi : attribute T -> attribute T.
Hypothesis Hrr : forall a, rhoi (rho a) = a.
Hypothesis Hrr' : forall b, rho (rhoi b) = b.
Hypothesis Hord : forall a b, Oset.compare (OAtt T) (rho a) (rho b) = Oset.compare (OAtt T) a b.
Hypothesis Hty : forall a, type_of_attribute T (rho a) = type_of_attribute T a.

Lemma rho_inj : forall a b, rho a = rho b -> a = b.
Proof. intros a b H; rewrite <- (Hrr a), <- (Hrr b), H; reflexivity. Qed.

Lemma rho_eqb : forall a b, Oset.eq_bool (OAtt T) (rho a) (rho b) = Oset.eq_bool (OAtt T) a b.
Proof. intros a b; unfold Oset.eq_bool; rewrite Hord; reflexivity. Qed.

(** the renamed sets *)
Definition rs (s : Fset.set (A T)) := Fset.mk_set (A T) (map rho ({{{s}}})).

Lemma mem_rs : forall s a, (rho a inS? rs s) = (a inS? s).
Proof.
intros s a; unfold rs; rewrite Fset.mem_mk_set, Fset.mem_elements.
induction ({{{s}}}) as [ | x l IH]; [reflexivity | ].
simpl; rewrite rho_eqb, IH; unfold Oset.eq_bool; reflexivity.
Qed.

Lemma mem_rs' : forall s b, (b inS? rs s) = (rhoi b inS? s).
Proof. intros s b; rewrite <- (Hrr' b) at 1; rewrite mem_rs; reflexivity. Qed.

Lemma rs_eq : forall s1 s2, s1 =S= s2 -> rs s1 =S= rs s2.
Proof. intros s1 s2 H; rewrite Fset.equal_spec; intro b; rewrite !mem_rs'; apply Fset.mem_eq_2; exact H. Qed.

Lemma rs_union : forall s1 s2, rs (s1 unionS s2) =S= (rs s1 unionS rs s2).
Proof. intros s1 s2; rewrite Fset.equal_spec; intro b; rewrite Fset.mem_union, !mem_rs', Fset.mem_union; reflexivity. Qed.

Lemma rs_singleton : forall a, rs (Fset.singleton (A T) a) =S= Fset.singleton (A T) (rho a).
Proof.
intro a; rewrite Fset.equal_spec; intro b; rewrite mem_rs', !Fset.singleton_spec.
rewrite <- (Hrr' b) at 2; rewrite rho_eqb; reflexivity.
Qed.

Lemma rs_mk_set : forall l, rs (Fset.mk_set (A T) l) =S= Fset.mk_set (A T) (map rho l).
Proof.
intro l; rewrite Fset.equal_spec; intro b; rewrite mem_rs', !Fset.mem_mk_set.
rewrite <- (Hrr' b) at 2; induction l as [ | x l IH]; [reflexivity | simpl; rewrite rho_eqb, IH; reflexivity].
Qed.

Lemma rs_empty : rs (Fset.empty (A T)) =S= Fset.empty (A T).
Proof. rewrite Fset.equal_spec; intro b; rewrite mem_rs', !Fset.empty_spec; reflexivity. Qed.

(** the elements of a renamed set, in order *)
Lemma sorted_map_rho : forall l, Sorted (fun x y => Oset.compare (OAtt T) x y = Lt) l ->
  Sorted (fun x y => Oset.compare (OAtt T) x y = Lt) (map rho l).
Proof.
intros l H; induction H as [ | x l H IH Hx]; simpl; constructor; [exact IH | ].
destruct Hx as [ | y l Hy]; constructor; rewrite Hord; exact Hy.
Qed.

Lemma sorted_same : forall l1 l2,
  Sorted (fun x y => Oset.compare (OAtt T) x y = Lt) l1 -> Sorted (fun x y => Oset.compare (OAtt T) x y = Lt) l2 ->
  (forall x, In x l1 <-> In x l2) -> l1 = l2.
Proof.
assert (Tr : Relations_1.Transitive (fun x y : attribute T => Oset.compare (OAtt T) x y = Lt))
  by (intros x y z; apply Oset.compare_lt_trans).
intros l1 l2 S1 S2; apply Sorted_StronglySorted in S1; [ | exact Tr]; apply Sorted_StronglySorted in S2; [ | exact Tr].
revert l2 S2; induction S1 as [ | x l1 S1 IH F1]; intros l2 S2 H.
- destruct l2 as [ | y l2]; [reflexivity | destruct (proj2 (H y) (or_introl eq_refl))].
- destruct S2 as [ | y l2 S2 F2]; [destruct (proj1 (H x) (or_introl eq_refl)) | ].
  assert (Exy : x = y).
  { destruct (proj1 (H x) (or_introl eq_refl)) as [E | I]; [exact (eq_sym E) | ].
    destruct (proj2 (H y) (or_introl eq_refl)) as [E | J]; [exact E | ].
    rewrite Forall_forall in F1, F2; generalize (F1 y J) (F2 x I); intros A1 A2.
    rewrite Oset.compare_lt_gt, A2 in A1; discriminate A1. }
  subst y; f_equal; apply IH; [exact S2 | ].
  intro z; split; intro Iz.
  + destruct (proj1 (H z) (or_intror Iz)) as [E | J]; [ | exact J].
    subst z; rewrite Forall_forall in F1; generalize (F1 x Iz); rewrite Oset.compare_eq_refl; discriminate.
  + destruct (proj2 (H z) (or_intror Iz)) as [E | J]; [ | exact J].
    subst z; rewrite Forall_forall in F2; generalize (F2 x Iz); rewrite Oset.compare_eq_refl; discriminate.
Qed.

Lemma in_elements_iff : forall (s : Fset.set (A T)) (x : attribute T), In x ({{{s}}}) <-> x inS s.
Proof.
intros s x; split; intro H; [apply Fset.in_elements_mem; exact H | apply Fset.mem_in_elements; exact H].
Qed.

Lemma elements_rs : forall s, {{{rs s}}} = map rho ({{{s}}}).
Proof.
intro s; apply sorted_same.
- apply Fset.elements_spec3.
- apply sorted_map_rho; apply Fset.elements_spec3.
- intro x; rewrite in_elements_iff; unfold rs; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff; tauto.
Qed.

(** the renamed tuples *)
Definition rt (t : tuple T) := mk_tuple T (rs (labels T t)) (fun b => dot T t (rhoi b)).

Lemma labels_rt : forall t, labels T (rt t) =S= rs (labels T t).
Proof. intro t; apply labels_mk_tuple. Qed.

Lemma dot_rt : forall t a, a inS labels T t -> dot T (rt t) (rho a) = dot T t a.
Proof. intros t a H; unfold rt; rewrite dot_mk_tuple, mem_rs, H, Hrr; reflexivity. Qed.

Lemma mem_rt : forall t a, (rho a inS? labels T (rt t)) = (a inS? labels T t).
Proof. intros t a; rewrite (Fset.mem_eq_2 _ _ _ (labels_rt t)); apply mem_rs. Qed.

(** two tuples related by the renaming *)
Definition RT (t' t : tuple T) := t' =t= rt t.

Lemma RT_labels : forall t' t, RT t' t -> labels T t' =S= rs (labels T t).
Proof.
intros t' t H; unfold RT in H; rewrite tuple_eq in H.
rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 H)); apply labels_rt.
Qed.

Lemma RT_mem : forall t' t a, RT t' t -> (rho a inS? labels T t') = (a inS? labels T t).
Proof. intros t' t a H; rewrite (Fset.mem_eq_2 _ _ _ (RT_labels _ _ H)); apply mem_rs. Qed.

Lemma RT_dot : forall t' t a, RT t' t -> a inS labels T t -> dot T t' (rho a) = dot T t a.
Proof.
intros t' t a H Ha; unfold RT in H; rewrite tuple_eq in H; rewrite (proj2 H).
- apply dot_rt; exact Ha.
- rewrite (Fset.mem_eq_2 _ _ _ (proj1 H)), (Fset.mem_eq_2 _ _ _ (labels_rt t)), mem_rs; exact Ha.
Qed.

(** a missing attribute of a tuple has the default value of its type *)
Hypothesis Hdot : forall t a, (a inS? labels T t) = false -> dot T t a = default_value T (type_of_attribute T a).

Lemma RT_dot_all : forall t' t a, RT t' t -> dot T t' (rho a) = dot T t a.
Proof.
intros t' t a H; destruct (a inS? labels T t) eqn:Ha; [apply RT_dot; assumption | ].
rewrite Hdot, Hdot, Hty; [reflexivity | exact Ha | rewrite (RT_mem _ _ _ H); exact Ha].
Qed.

Lemma RT_dot' : forall t' t b, RT t' t -> dot T t' b = dot T t (rhoi b).
Proof. intros t' t b H; rewrite <- (Hrr' b) at 1; apply RT_dot_all; exact H. Qed.

Lemma RT_intro : forall t' t, labels T t' =S= rs (labels T t) -> (forall a, a inS labels T t -> dot T t' (rho a) = dot T t a) ->
  RT t' t.
Proof.
intros t' t Hl Hd; unfold RT; rewrite tuple_eq; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ Hl), (Fset.equal_eq_2 _ _ _ _ (labels_rt t)); apply Fset.equal_refl.
- intros b Hb; rewrite (Fset.mem_eq_2 _ _ _ Hl), mem_rs' in Hb.
  rewrite <- (Hrr' b), Hd, dot_rt; [reflexivity | exact Hb | exact Hb].
Qed.

Lemma RT_rt : forall t, RT (rt t) t.
Proof. intro t; apply Oeset.compare_eq_refl. Qed.

Lemma RT_eq_l : forall t1' t2' t, t1' =t= t2' -> RT t2' t -> RT t1' t.
Proof. intros t1' t2' t E H; unfold RT in *; eapply Oeset.compare_eq_trans; eassumption. Qed.

Lemma RT_eq_r : forall t' t1 t2, t1 =t= t2 -> RT t' t1 -> RT t' t2.
Proof.
intros t' t1 t2 E H; apply RT_intro.
- rewrite (Fset.equal_eq_1 _ _ _ _ (RT_labels _ _ H)); apply rs_eq; rewrite tuple_eq in E; exact (proj1 E).
- intros a Ha; rewrite (RT_dot_all _ _ _ H); rewrite tuple_eq in E; apply (proj2 E).
  rewrite (Fset.mem_eq_2 _ _ _ (proj1 E)); exact Ha.
Qed.

Lemma RT_mk_tuple : forall s s' f f', s' =S= rs s -> (forall a, a inS s -> f' (rho a) = f a) ->
  RT (mk_tuple T s' f') (mk_tuple T s f).
Proof.
intros s s' f f' Hs Hf; apply RT_intro.
- rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)); rewrite (Fset.equal_eq_1 _ _ _ _ Hs).
  apply rs_eq; rewrite Fset.equal_spec; intro x; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)); reflexivity.
- intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha; rewrite !dot_mk_tuple.
  rewrite (Fset.mem_eq_2 _ _ _ Hs), mem_rs, Ha; apply Hf; exact Ha.
Qed.

Lemma RT_join : forall t1' t1 t2' t2, RT t1' t1 -> RT t2' t2 -> RT (join_tuple T t1' t2') (join_tuple T t1 t2).
Proof.
intros t1' t1 t2' t2 H1 H2; unfold join_tuple; apply RT_mk_tuple.
- rewrite Fset.equal_spec; intro b; rewrite Fset.mem_union, !mem_rs', Fset.mem_union.
  rewrite <- (Hrr' b) at 1 2; rewrite (RT_mem _ _ _ H1), (RT_mem _ _ _ H2); reflexivity.
- intros a _; rewrite (RT_mem _ _ _ H1); destruct (a inS? labels T t1); [apply RT_dot_all | apply RT_dot_all]; assumption.
Qed.

Lemma RT_empty : RT (empty_tuple T) (empty_tuple T).
Proof.
unfold empty_tuple; apply RT_mk_tuple; [ | intros; rewrite Hty; reflexivity].
rewrite Fset.equal_spec; intro b; rewrite mem_rs', !Fset.empty_spec; reflexivity.
Qed.

(** two related tuples are equal when the tuples they rename are *)
Lemma RT_compare : forall t1' t1 t2' t2, RT t1' t1 -> RT t2' t2 ->
  (Oeset.compare (OTuple T) t1' t2' = Eq <-> Oeset.compare (OTuple T) t1 t2 = Eq).
Proof.
intros t1' t1 t2' t2 H1 H2; rewrite !tuple_eq; split; intros [L D].
- split.
  + rewrite Fset.equal_spec; intro a; rewrite <- (RT_mem _ _ _ H1), <- (RT_mem _ _ _ H2); apply Fset.mem_eq_2; exact L.
  + intros a Ha; rewrite <- (RT_dot_all _ _ _ H1), <- (RT_dot_all _ _ _ H2); apply D; rewrite (RT_mem _ _ _ H1); exact Ha.
- split.
  + rewrite Fset.equal_spec; intro b; rewrite <- (Hrr' b), (RT_mem _ _ _ H1), (RT_mem _ _ _ H2); apply Fset.mem_eq_2; exact L.
  + intros b Hb; rewrite (RT_dot' _ _ _ H1), (RT_dot' _ _ _ H2); apply D.
    rewrite <- (RT_mem _ _ _ H1), Hrr'; exact Hb.
Qed.

Lemma RT_eq_bool : forall t1' t1 t2' t2, RT t1' t1 -> RT t2' t2 ->
  Oeset.eq_bool (OTuple T) t1' t2' = Oeset.eq_bool (OTuple T) t1 t2.
Proof.
intros t1' t1 t2' t2 H1 H2; generalize (RT_compare _ _ _ _ H1 H2); unfold Oeset.eq_bool.
destruct (Oeset.compare (OTuple T) t1' t2'); destruct (Oeset.compare (OTuple T) t1 t2); intros [A B];
  try reflexivity; [discriminate (A eq_refl) | discriminate (A eq_refl) | discriminate (B eq_refl) | discriminate (B eq_refl)].
Qed.

Lemma elements_labels_RT : forall t' t, RT t' t -> {{{labels T t'}}} = map rho ({{{labels T t}}}).
Proof. intros t' t H; rewrite <- elements_rs; apply (Fset.elements_spec1 _ _ _ (RT_labels _ _ H)). Qed.

(** lists of related tuples *)
Definition RL := Forall2 RT.

Lemma RL_map : forall (X Y : Type) (f : X -> tuple T) (g : Y -> tuple T) (P : X -> Y -> Prop) l1 l2,
  Forall2 P l1 l2 -> (forall x y, P x y -> RT (f x) (g y)) -> RL (map f l1) (map g l2).
Proof. intros X Y f g P l1 l2 H K; induction H; constructor; auto. Qed.

Lemma RL_app : forall l1 l2 l1' l2', RL l1 l2 -> RL l1' l2' -> RL (l1 ++ l1') (l2 ++ l2').
Proof. intros; apply Forall2_app; assumption. Qed.

End Tuples.
