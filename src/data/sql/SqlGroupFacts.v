(** * The grouping of [SqlFull.v] by a balanced tree is the grouping by a list (TODO 6.6)

    [group_on] keeps the groups in an AVL tree ([FiniteSetImpl]) indexed by the canonical keys; [group_on_list]
    inserts each element in a list of groups. [group_on_spec]: they are the same, the groups of the keys in the
    order of their first occurrence, each with its elements in the order of the list. *)
Require Import List Bool Lia SetoidList.
Require Import BasicFacts ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection FlatData SqlFull.
Require FiniteSetImpl.

Section Sec.

Hypothesis T : Tuple.Rcd.
Hypothesis O : dialect T.
Variable X : Type.

Import Tuple.

Notation value := (value T).
Notation tree := (FiniteSetImpl.tree (list value * list X)).
Notation OF := (OFst T X).
Notation OK := (OKey T).
Notation tfind := (tfind T (X := X)).
Notation tupdate := (tupdate T (X := X)).

Lemma ok_eq : forall a b, Oset.compare OK a b = Eq <-> a = b.
Proof. intros a b; apply Oset.compare_eq_iff. Qed.

Lemma of_compare : forall p q, Oeset.compare OF p q = Oset.compare OK (fst p) (fst q).
Proof. intros; reflexivity. Qed.

(** ** [tfind] and the elements of the tree *)

Lemma tfind_some :
  forall t c y, FiniteSetImpl.Ok OF t ->
    (tfind c t = Some y <-> List.In y (FiniteSetImpl.elements t) /\ fst y = c).
Proof.
intro t; induction t as [ | l IHl y0 r IHr h]; intros c y Ok.
- simpl; split; [discriminate | intros [K _]; contradiction K].
- inversion Ok as [ | ? ? ? ? Bl Br Lt Gt]; subst.
  assert (E : FiniteSetImpl.elements (FiniteSetImpl.Node l y0 r h) =
              FiniteSetImpl.elements l ++ y0 :: FiniteSetImpl.elements r).
  { rewrite <- (app_nil_r (FiniteSetImpl.elements (FiniteSetImpl.Node l y0 r h))),
      <- FiniteSetImpl.elements_node, app_nil_r; reflexivity. }
  rewrite E; cbn [SqlFull.tfind].
  case_eq (Oset.compare OK c (fst y0)); intro K.
  + apply ok_eq in K; subst c; split.
    * intro H; injection H; intros <-; split; [apply in_or_app; right; left; reflexivity | reflexivity].
    * intros [H F]; f_equal.
      apply in_app_or in H; destruct H as [H | [H | H]]; trivial.
      -- assert (I : FiniteSetImpl.InT OF y l)
           by (apply FiniteSetImpl.elements_spec1; apply In_InA; [apply (FiniteSetImpl.equiv_eq_elt OF) | exact H]).
         generalize (Lt _ I); rewrite of_compare, F, Oset.compare_eq_refl; discriminate.
      -- assert (I : FiniteSetImpl.InT OF y r)
           by (apply FiniteSetImpl.elements_spec1; apply In_InA; [apply (FiniteSetImpl.equiv_eq_elt OF) | exact H]).
         generalize (Gt _ I); rewrite of_compare, F, Oset.compare_eq_refl; discriminate.
  + rewrite IHl; [ | exact Bl]; split.
    * intros [H F]; split; [apply in_or_app; left; exact H | exact F].
    * intros [H F]; split; [ | exact F].
      apply in_app_or in H; destruct H as [H | [H | H]]; trivial.
      -- subst y; rewrite F, Oset.compare_eq_refl in K; discriminate.
      -- assert (I : FiniteSetImpl.InT OF y r)
           by (apply FiniteSetImpl.elements_spec1; apply In_InA; [apply (FiniteSetImpl.equiv_eq_elt OF) | exact H]).
         generalize (Gt _ I); rewrite of_compare, F; rewrite Oset.compare_lt_gt, K; discriminate.
  + rewrite IHr; [ | exact Br]; split.
    * intros [H F]; split; [apply in_or_app; right; right; exact H | exact F].
    * intros [H F]; split; [ | exact F].
      apply in_app_or in H; destruct H as [H | [H | H]]; trivial.
      -- assert (I : FiniteSetImpl.InT OF y l)
           by (apply FiniteSetImpl.elements_spec1; apply In_InA; [apply (FiniteSetImpl.equiv_eq_elt OF) | exact H]).
         generalize (Lt _ I); rewrite of_compare, F, K; discriminate.
      -- subst y; rewrite F, Oset.compare_eq_refl in K; discriminate.
Qed.

Lemma tfind_none :
  forall t c g, FiniteSetImpl.Ok OF t -> tfind c t = None -> ~ FiniteSetImpl.InT OF (c, g) t.
Proof.
intros t c g Ok H I.
apply FiniteSetImpl.elements_spec1 in I; apply InA_alt in I; destruct I as [y [E I]].
rewrite of_compare in E; apply ok_eq in E; simpl in E.
assert (K := proj2 (tfind_some t c y Ok) (conj I (eq_sym E))); rewrite H in K; discriminate.
Qed.

(** ** [tupdate]: the group of a key replaced in place *)

Lemma tfind_tupdate_same :
  forall t c g, (exists y, tfind c t = Some y) -> tfind c (tupdate c g t) = Some (c, g).
Proof.
intro t; induction t as [ | l IHl y0 r IHr h]; intros c g [y H]; [discriminate H | ].
cbn [SqlFull.tfind SqlFull.tupdate] in *.
destruct (Oset.compare OK c (fst y0)) eqn:K.
- cbn [SqlFull.tfind fst]; rewrite Oset.compare_eq_refl; reflexivity.
- cbn [SqlFull.tfind]; rewrite K; apply IHl; exists y; exact H.
- cbn [SqlFull.tfind]; rewrite K; apply IHr; exists y; exact H.
Qed.

Lemma tfind_tupdate_other :
  forall t c c' g, c' <> c -> tfind c' (tupdate c g t) = tfind c' t.
Proof.
intro t; induction t as [ | l IHl y0 r IHr h]; intros c c' g D; [reflexivity | ].
cbn [SqlFull.tfind SqlFull.tupdate].
destruct (Oset.compare OK c (fst y0)) eqn:K.
- apply ok_eq in K; cbn [SqlFull.tfind fst]; rewrite K.
  destruct (Oset.compare OK c' (fst y0)) eqn:K'; trivial.
  apply ok_eq in K'; exfalso; apply D; congruence.
- cbn [SqlFull.tfind]; destruct (Oset.compare OK c' (fst y0)); trivial; apply IHl; exact D.
- cbn [SqlFull.tfind]; destruct (Oset.compare OK c' (fst y0)); trivial; apply IHr; exact D.
Qed.

Lemma InT_tupdate :
  forall t c g z, FiniteSetImpl.InT OF z (tupdate c g t) <-> FiniteSetImpl.InT OF z t.
Proof.
intro t; induction t as [ | l IHl y0 r IHr h]; intros c g z; [reflexivity | ].
cbn [SqlFull.tupdate].
destruct (Oset.compare OK c (fst y0)) eqn:K; split; intro I; inversion I; subst.
- apply FiniteSetImpl.IsRoot; rewrite of_compare in *; simpl in *; apply ok_eq in K; rewrite <- K; trivial.
- apply FiniteSetImpl.InLeft; trivial.
- apply FiniteSetImpl.InRight; trivial.
- apply FiniteSetImpl.IsRoot; rewrite of_compare in *; simpl; apply ok_eq in K; rewrite K; trivial.
- apply FiniteSetImpl.InLeft; trivial.
- apply FiniteSetImpl.InRight; trivial.
- apply FiniteSetImpl.IsRoot; trivial.
- apply FiniteSetImpl.InLeft; rewrite IHl in *; trivial.
- apply FiniteSetImpl.InRight; trivial.
- apply FiniteSetImpl.IsRoot; trivial.
- apply FiniteSetImpl.InLeft; rewrite IHl; trivial.
- apply FiniteSetImpl.InRight; trivial.
- apply FiniteSetImpl.IsRoot; trivial.
- apply FiniteSetImpl.InLeft; trivial.
- apply FiniteSetImpl.InRight; rewrite IHr in *; trivial.
- apply FiniteSetImpl.IsRoot; trivial.
- apply FiniteSetImpl.InLeft; trivial.
- apply FiniteSetImpl.InRight; rewrite IHr; trivial.
Qed.

Lemma tupdate_ok :
  forall t c g, FiniteSetImpl.Ok OF t -> FiniteSetImpl.Ok OF (tupdate c g t).
Proof.
intro t; induction t as [ | l IHl y0 r IHr h]; intros c g Ok; [exact Ok | ].
inversion Ok as [ | ? ? ? ? Bl Br Lt Gt]; subst.
cbn [SqlFull.tupdate]; destruct (Oset.compare OK c (fst y0)) eqn:K.
- apply ok_eq in K; constructor; trivial.
  + intros z I; generalize (Lt z I); rewrite !of_compare; simpl; rewrite K; trivial.
  + intros z I; generalize (Gt z I); rewrite !of_compare; simpl; rewrite K; trivial.
- constructor; trivial; [apply IHl; exact Bl | ].
  intros z I; apply Lt; rewrite InT_tupdate in I; exact I.
- constructor; trivial; [apply IHr; exact Br | ].
  intros z I; apply Gt; rewrite InT_tupdate in I; exact I.
Qed.

(** ** [add] of a new key *)

Lemma tfind_add :
  forall t c g c', FiniteSetImpl.Ok OF t -> tfind c t = None ->
    tfind c' (FiniteSetImpl.add OF (c, g) t) = if Oset.eq_bool OK c' c then Some (c, g) else tfind c' t.
Proof.
intros t c g c' Ok N.
assert (Ok' := FiniteSetImpl.add_ok (c, g) Ok).
assert (A := @FiniteSetImpl.add_spec'' _ OF (c, g) t (tfind_none t c g Ok N)).
case_eq (Oset.eq_bool OK c' c); intro E.
- rewrite Oset.eq_bool_true_iff in E; subst c'.
  apply (proj2 (tfind_some _ c (c, g) Ok')); split; [apply A; left; reflexivity | reflexivity].
- assert (D : c' <> c) by (intro K; subst; rewrite Oset.eq_bool_refl in E; discriminate E).
  case_eq (tfind c' t).
  + intros y Y; apply (proj1 (tfind_some _ c' y Ok)) in Y; destruct Y as [Y F].
    apply (proj2 (tfind_some _ c' y Ok')); split; [apply A; right; exact Y | exact F].
  + intro Y; case_eq (tfind c' (FiniteSetImpl.add OF (c, g) t)); [ | reflexivity].
    intros y K; apply (proj1 (tfind_some _ c' y Ok')) in K; destruct K as [K F].
    apply A in K; destruct K as [K | K].
    * subst y; contradiction D; exact (eq_sym F).
    * rewrite (proj2 (tfind_some _ c' y Ok) (conj K F)) in Y; discriminate Y.
Qed.

(** ** The groups *)

Variable key : X -> list value.

Definition ck (x : X) := map (canon O) (key x).
Definition eqk (a b : list value) := Oset.eq_bool OK a b.
(** the elements of [p] of canonical key [c] *)
Definition G (p : list X) (c : list value) := filter (fun x => eqk (ck x) c) p.

Lemma eqk_iff : forall a b, eqk a b = true <-> a = b.
Proof. intros; apply Oset.eq_bool_true_iff. Qed.

Lemma eqk_refl : forall a, eqk a a = true.
Proof. intro; apply eqk_iff; reflexivity. Qed.

Lemma eqk_sym : forall a b, eqk a b = eqk b a.
Proof.
intros a b; case_eq (eqk b a); intro E; [apply eqk_iff in E; subst; apply eqk_refl | ].
case_eq (eqk a b); intro F; [apply eqk_iff in F; subst; rewrite eqk_refl in E; discriminate | reflexivity].
Qed.

Lemma G_app_x :
  forall p x c, G (p ++ x :: nil) c = G p c ++ (if eqk (ck x) c then x :: nil else nil).
Proof. intros; unfold G; rewrite filter_app; reflexivity. Qed.

(** the representatives of the groups: the first element of each key *)
Fixpoint firsts_acc (acc l : list X) : list X :=
  match l with
  | nil => acc
  | x :: l => firsts_acc (if existsb (fun r => eqk (ck r) (ck x)) acc then acc else acc ++ x :: nil) l
  end.

Definition Fp (p : list X) (r : X) := (key r, G p (ck r)).

Lemma group_insert_spec :
  forall acc p x, NoDup (map ck acc) ->
    (existsb (fun r => eqk (ck r) (ck x)) acc = false -> G p (ck x) = nil) ->
    group_insert O (key x) x (map (Fp p) acc) =
    map (Fp (p ++ x :: nil)) (if existsb (fun r => eqk (ck r) (ck x)) acc then acc else acc ++ x :: nil).
Proof.
intro acc; induction acc as [ | r acc IH]; intros p x D H.
- simpl; unfold Fp; rewrite G_app_x, H, eqk_refl; reflexivity.
- simpl in D; inversion D as [ | ? ? Nr Dacc]; subst.
  cbn [map group_insert existsb]; unfold Fp at 1.
  replace (key_eqb O (key x) (key r)) with (eqk (ck r) (ck x)) by (rewrite eqk_sym; reflexivity).
  case_eq (eqk (ck r) (ck x)); intro E; cbn [orb map].
  + unfold Fp at 2; rewrite G_app_x, (eqk_sym (ck x)), E; f_equal.
    apply map_ext_in; intros r' I; unfold Fp; rewrite G_app_x.
    case_eq (eqk (ck x) (ck r')); intro E'; [ | rewrite app_nil_r; reflexivity].
    apply eqk_iff in E; apply eqk_iff in E'; contradiction Nr; rewrite E, E'; apply in_map; exact I.
  + destruct (existsb (fun r0 => eqk (ck r0) (ck x)) acc) eqn:Ex; cbn [map app];
      unfold Fp at 2; rewrite G_app_x, (eqk_sym (ck x)), E, app_nil_r; f_equal;
      (rewrite IH; [rewrite Ex; reflexivity | exact Dacc | ]).
    * intro K; rewrite Ex in K; discriminate K.
    * intro K; apply H; cbn [existsb]; rewrite E, K; reflexivity.
Qed.

(** the invariant of the representatives: their keys are distinct and they cover the elements seen *)
Definition reps_ok (p acc : list X) :=
  NoDup (map ck acc) /\ (forall y, In y p -> existsb (fun r => eqk (ck r) (ck y)) acc = true).

Lemma NoDup_snoc : forall (A : Type) (l : list A) a, NoDup l -> ~ In a l -> NoDup (l ++ a :: nil).
Proof.
intros A l a D N; induction D as [ | b l Nb D IH]; [constructor; [intro K; contradiction K | constructor] | ].
simpl; constructor; [ | apply IH; intro K; apply N; right; exact K].
intro K; apply in_app_or in K; destruct K as [K | [K | K]]; [contradiction | subst; apply N; left; reflexivity | contradiction].
Qed.

Lemma reps_ok_step :
  forall p acc x, reps_ok p acc ->
    reps_ok (p ++ x :: nil) (if existsb (fun r => eqk (ck r) (ck x)) acc then acc else acc ++ x :: nil).
Proof.
intros p acc x [D C]; case_eq (existsb (fun r => eqk (ck r) (ck x)) acc); intro E; split.
- exact D.
- intros y I; apply in_app_or in I; destruct I as [I | [I | I]]; [apply C; exact I | subst; exact E | contradiction I].
- rewrite map_app; apply NoDup_snoc; trivial.
  intro Ia; apply in_map_iff in Ia; destruct Ia as [r [Er Ir]].
  assert (K : existsb (fun r => eqk (ck r) (ck x)) acc = true)
    by (apply existsb_exists; exists r; split; [exact Ir | rewrite Er; apply eqk_refl]).
  rewrite K in E; discriminate E.
- intros y I; rewrite existsb_app; apply in_app_or in I; destruct I as [I | [I | I]].
  + rewrite (C y I); reflexivity.
  + subst; cbn [existsb]; rewrite eqk_refl, orb_true_r; reflexivity.
  + contradiction I.
Qed.

Lemma uncovered :
  forall p acc x, reps_ok p acc -> existsb (fun r => eqk (ck r) (ck x)) acc = false -> G p (ck x) = nil.
Proof.
intros p acc x [_ C] E; unfold G.
assert (C' : forall y, In y p -> eqk (ck y) (ck x) = false).
{ intros y I; case_eq (eqk (ck y) (ck x)); intro K; [ | reflexivity].
  apply eqk_iff in K; rewrite <- K in E; rewrite (C y I) in E; discriminate E. }
clear C E; induction p as [ | y p IH]; [reflexivity | ].
simpl; rewrite (C' y (or_introl eq_refl)); apply IH; intros z I; apply C'; right; exact I.
Qed.

Lemma list_fold :
  forall l p acc, reps_ok p acc ->
    fold_left (fun gs x => group_insert O (key x) x gs) l (map (Fp p) acc) = map (Fp (p ++ l)) (firsts_acc acc l).
Proof.
intro l; induction l as [ | x l IH]; intros p acc R; [rewrite app_nil_r; reflexivity | ].
cbn [fold_left firsts_acc].
rewrite group_insert_spec; [ | apply R | apply uncovered; exact R].
rewrite IH; [ | apply reps_ok_step; exact R].
rewrite <- app_assoc; reflexivity.
Qed.

Definition tree_ok (p acc : list X) (t : tree) :=
  FiniteSetImpl.Ok OF t /\
  forall c, tfind c t = if existsb (fun r => eqk (ck r) c) acc then Some (c, rev (G p c)) else None.

Lemma tree_fold :
  forall l p acc t, reps_ok p acc -> tree_ok p acc t ->
    exists t', gfold O key t (rev acc) l = (t', rev (firsts_acc acc l)) /\ tree_ok (p ++ l) (firsts_acc acc l) t'.
Proof.
intro l; induction l as [ | x l IH]; intros p acc t R [Ok Inv].
- exists t; rewrite app_nil_r; split; [reflexivity | split; trivial].
- cbn [gfold firsts_acc]; fold (ck x); rewrite (Inv (ck x)).
  case_eq (existsb (fun r => eqk (ck r) (ck x)) acc); intro E.
  + destruct (IH (p ++ x :: nil) acc (tupdate (ck x) (x :: rev (G p (ck x))) t)) as [t' [H1 H2]].
    * generalize (reps_ok_step p acc x R); rewrite E; trivial.
    * split; [apply tupdate_ok; exact Ok | intro c].
      case_eq (eqk (ck x) c); intro K.
      -- apply eqk_iff in K; subst c; rewrite tfind_tupdate_same; [ | rewrite (Inv (ck x)), E; eexists; reflexivity].
         rewrite E, G_app_x, eqk_refl, rev_app_distr; reflexivity.
      -- rewrite tfind_tupdate_other; [ | intro D; subst c; rewrite eqk_refl in K; discriminate K].
         rewrite Inv, G_app_x, K, app_nil_r; reflexivity.
    * exists t'; rewrite <- app_assoc in H2; split; [exact H1 | exact H2].
  + destruct (IH (p ++ x :: nil) (acc ++ x :: nil) (FiniteSetImpl.add OF (ck x, x :: nil) t)) as [t' [H1 H2]].
    * generalize (reps_ok_step p acc x R); rewrite E; trivial.
    * split; [apply FiniteSetImpl.add_ok; exact Ok | intro c].
      rewrite tfind_add; trivial; [ | rewrite Inv, E; reflexivity].
      rewrite existsb_app; cbn [existsb]; rewrite orb_false_r.
      case_eq (Oset.eq_bool OK c (ck x)); intro K.
      -- apply Oset.eq_bool_true_iff in K; subst c; rewrite E, eqk_refl; simpl.
         rewrite G_app_x, eqk_refl, (uncovered p acc x R E); reflexivity.
      -- assert (K' : eqk (ck x) c = false) by (unfold eqk; rewrite <- K; apply eqk_sym).
         rewrite K', orb_false_r, Inv, G_app_x, K', app_nil_r; reflexivity.
    * exists t'; split.
      -- rewrite <- H1; f_equal; rewrite rev_app_distr; reflexivity.
      -- rewrite <- app_assoc in H2; exact H2.
Qed.

(** [group_on] (the tree) is [group_on_list] (the list of groups) *)
Theorem group_on_spec : forall l, group_on O key l = group_on_list O key l.
Proof.
intro l; unfold group_on, group_on_list.
assert (R0 : reps_ok nil nil) by (split; [constructor | intros y I; contradiction I]).
assert (T0 : tree_ok nil nil (FiniteSetImpl.Leaf _)) by (split; [constructor | intro c; reflexivity]).
destruct (tree_fold l nil nil _ R0 T0) as [t' [H1 [_ H2]]].
change (rev (@nil X)) with (@nil X) in H1; rewrite H1, rev_involutive.
change (fold_left (fun gs x => group_insert O (key x) x gs) l nil) with
       (fold_left (fun gs x => group_insert O (key x) x gs) l (map (Fp nil) nil)).
rewrite list_fold; [ | exact R0].
rewrite map_map; apply map_ext_in; intros r I; fold (ck r).
rewrite H2; replace (existsb (fun r0 => eqk (ck r0) (ck r)) (firsts_acc nil l)) with true.
- rewrite rev_involutive; reflexivity.
- symmetry; apply existsb_exists; exists r; split; [exact I | apply eqk_refl].
Qed.

End Sec.
