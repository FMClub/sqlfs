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
assert (RV : forall (A : Type) (k : list A), rev' k = rev k) by (intros; symmetry; apply rev_alt).
assert (R0 : reps_ok nil nil) by (split; [constructor | intros y I; contradiction I]).
assert (T0 : tree_ok nil nil (FiniteSetImpl.Leaf _)) by (split; [constructor | intro c; reflexivity]).
destruct (tree_fold l nil nil _ R0 T0) as [t' [H1 [_ H2]]].
change (rev (@nil X)) with (@nil X) in H1; rewrite H1, RV, rev_involutive.
change (fold_left (fun gs x => group_insert O (key x) x gs) l nil) with
       (fold_left (fun gs x => group_insert O (key x) x gs) l (map (Fp nil) nil)).
rewrite list_fold; [ | exact R0].
rewrite map_map; apply map_ext_in; intros r I; fold (ck r).
rewrite H2; replace (existsb (fun r0 => eqk (ck r0) (ck r)) (firsts_acc nil l)) with true.
- rewrite RV, rev_involutive; reflexivity.
- symmetry; apply existsb_exists; exists r; split; [exact I | apply eqk_refl].
Qed.

End Sec.

(** * The grouping sets of [ROLLUP] (TODO 6.4)

    [rollup_groupings]: the groups of [GROUP BY ROLLUP (e1, ..., en)] are, for [k] from [n] down to [0], the
    groups of [GROUP BY e1, ..., ek] (all the rows for [k = 0]), in which the expressions [e(k+1), ..., en]
    are hidden (NULL): [ROLLUP] is the [UNION ALL] of the groupings by its prefixes. *)
Section Rollup.

Hypothesis T : Tuple.Rcd.
Hypothesis O : dialect T.
Hypothesis relname : Type.

Import Tuple.

Notation sexpr := (sexpr T relname).

Lemma group_on_list_ext :
  forall (X : Type) (k1 k2 : X -> list (value T)) l, (forall x, k1 x = k2 x) ->
    group_on_list O k1 l = group_on_list O k2 l.
Proof.
intros X k1 k2 l H; unfold group_on_list; f_equal.
generalize (@nil (list (value T) * list X)); induction l as [ | x l IH]; intro acc; [reflexivity | ].
simpl; rewrite H; apply IH.
Qed.

Lemma group_on_ext :
  forall (X : Type) (k1 k2 : X -> list (value T)) l, (forall x, k1 x = k2 x) -> group_on O k1 l = group_on O k2 l.
Proof. intros X k1 k2 l H; rewrite !group_on_spec; apply group_on_list_ext; exact H. Qed.

Lemma skipn_nth :
  forall (A : Type) (l : list A) s d, s < length l -> skipn s l = nth s l d :: skipn (S s) l.
Proof.
intros A l; induction l as [ | a l IH]; intros s d H; [simpl in H; lia | ].
destruct s as [ | s]; [reflexivity | ]; simpl in *; apply IH; lia.
Qed.

Lemma map_nth_seq :
  forall (A : Type) (l : list A) d k s, s + k <= length l ->
    map (fun i => nth i l d) (seq s k) = firstn k (skipn s l).
Proof.
intros A l d k; induction k as [ | k IH]; intros s H; [reflexivity | ].
simpl; rewrite (@skipn_nth _ l s d) by lia; simpl; f_equal; apply IH; lia.
Qed.

Lemma map_nth_prefix :
  forall (A : Type) (l : list A) d k, k <= length l -> map (fun i => nth i l d) (seq 0 k) = firstn k l.
Proof. intros A l d k H; rewrite map_nth_seq by lia; reflexivity. Qed.

Lemma firstn_seq0 : forall n k, k <= n -> firstn k (seq 0 n) = seq 0 k.
Proof.
intros n k H; rewrite <- (@map_nth_prefix _ (seq 0 n) 0 k) by (rewrite seq_length; exact H).
transitivity (map (fun i => i) (seq 0 k)); [ | rewrite map_id; reflexivity].
apply map_ext_in; intros i I; apply in_seq in I; rewrite seq_nth by lia; reflexivity.
Qed.

Lemma flat_map_map' :
  forall (A B C : Type) (f : B -> list C) (g : A -> B) (l : list A), flat_map f (map g l) = flat_map (fun x => f (g x)) l.
Proof. intros A B C f g l; induction l as [ | x l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma flat_map_ext_in' :
  forall (A B : Type) (f g : A -> list B) (l : list A), (forall x, In x l -> f x = g x) -> flat_map f l = flat_map g l.
Proof.
intros A B f g l H; induction l as [ | x l IH]; simpl; [reflexivity | ].
rewrite (H x (or_introl eq_refl)), IH; [reflexivity | intros y I; apply H; right; exact I].
Qed.

Theorem rollup_groupings :
  forall (f : sexpr -> tuple T -> value T) (l : list sexpr) (rows : list (tuple T)),
    set_groupings O (fun t => map (fun e => f e t) l) l (rollup_sets (seq 0 (length l))) rows =
    flat_map (fun k =>
                let set := firstn k l in
                let hid := sdedup nil (filter (fun e => negb (existsb (sexpr_eqb e) set)) l) in
                map (fun grp => (grp, hid))
                    (match k with
                     | 0 => rows :: nil
                     | _ => group_on O (fun t => map (fun e => f e t) (firstn k l)) rows
                     end))
             (rev (seq 0 (S (length l)))).
Proof.
intros f l rows; unfold set_groupings, rollup_sets; rewrite flat_map_map', seq_length.
apply flat_map_ext_in'; intros k I; rewrite <- in_rev, in_seq in I.
assert (K : k <= length l) by lia.
rewrite (firstn_seq0 (length l) k K), (@map_nth_prefix _ l _ k K).
destruct k as [ | k]; [reflexivity | ].
cbn zeta; f_equal; apply group_on_ext; intro t.
rewrite (@map_nth_prefix _ (map (fun e => f e t) l)) by (rewrite map_length; exact K).
apply firstn_map.
Qed.

End Rollup.

(** * [ROLLUP] is the [GROUPING SETS] of its prefixes, at the level of the rows of a block (TODO 6.4)

    [rollup_as_grouping_sets]: a block with [GROUP BY ROLLUP (e1, ..., en)] gives the rows of the same block
    with [GROUP BY GROUPING SETS ((e1, ..., en), ..., (e1), ())], when the grouping expressions are columns,
    constants or functions of them (the expressions which [sexpr_eqb] identifies with themselves). *)
Section RollupRows.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.
Hypothesis ORN : Oset.Rcd relname.
Hypothesis O : dialect T.
Hypothesis basesort : relname -> Fset.set (Tuple.A T).
Hypothesis instance : relname -> Febag.bag (Fecol.CBag (Tuple.CTuple T)).

Import Tuple.

Notation sexpr := (sexpr T relname).

Lemma sdedup_app :
  forall (la lb : list sexpr) seen,
    (forall y, In y lb -> sexpr_eqb y y = true /\ (existsb (sexpr_eqb y) seen = true \/ In y la)) ->
    (forall y, In y la -> sexpr_eqb y y = true) ->
    sdedup seen (la ++ lb) = sdedup seen la.
Proof.
intro la; induction la as [ | x la IH]; intros lb seen H R.
- simpl; induction lb as [ | y lb IHb]; [reflexivity | ].
  simpl; destruct (H y (or_introl eq_refl)) as [_ [K | K]]; [ | contradiction K].
  rewrite K; apply IHb; intros z I; apply H; right; exact I.
- simpl; case_eq (existsb (sexpr_eqb x) seen); intro E.
  + apply IH; [ | intros y I; apply R; right; exact I].
    intros y I; destruct (H y I) as [Ry [K | [K | K]]]; split; trivial; [left; exact K | | right; exact K].
    subst; left; exact E.
  + f_equal; apply IH; [ | intros y I; apply R; right; exact I].
    intros y I; destruct (H y I) as [Ry [K | [K | K]]]; split; trivial.
    * left; simpl; rewrite K; apply Bool.orb_true_r.
    * subst; left; simpl; rewrite Ry; reflexivity.
    * right; exact K.
Qed.

Lemma in_firstn' : forall (A : Type) (l : list A) k x, In x (firstn k l) -> In x l.
Proof.
intros A l k x I; rewrite <- (firstn_skipn k l); apply in_or_app; left; exact I.
Qed.

Lemma concat_rollup :
  forall (l : list sexpr),
    exists rest, concat (rollup_sets l) = l ++ rest /\ (forall y, In y rest -> In y l).
Proof.
intro l; unfold rollup_sets.
rewrite seq_S, rev_app_distr; simpl; rewrite firstn_all.
exists (concat (map (fun n => firstn n l) (rev (seq 0 (length l))))); split; [reflexivity | ].
intros y I; apply in_concat in I; destruct I as [z [Iz Iy]]; apply in_map_iff in Iz.
destruct Iz as [k [Ek _]]; subst; exact (in_firstn' _ _ _ _ Iy).
Qed.

Lemma map_seq_shift :
  forall (A : Type) (g : nat -> A) off n, map g (seq off n) = map (fun j => g (off + j)) (seq 0 n).
Proof.
intros A g off n; revert g off; induction n as [ | n IH]; intros g off; [reflexivity | ].
simpl; rewrite <- plus_n_O; f_equal.
rewrite (IH g (S off)), (IH (fun j => g (off + j)) 1); apply map_ext; intro j; f_equal; lia.
Qed.

Lemma nth_concat_block :
  forall (A : Type) (pre : list (list A)) x r d j, j < length x ->
    nth (length (concat pre) + j) (concat (pre ++ x :: r)) d = nth j x d.
Proof.
intros A pre x r d j H; rewrite concat_app, app_nth2 by lia.
replace (length (concat pre) + j - length (concat pre)) with j by lia.
simpl; rewrite app_nth1 by exact H; reflexivity.
Qed.

Lemma block_of_positions :
  forall (A : Type) (pre : list (list A)) x r d,
    map (fun i => nth i (concat (pre ++ x :: r)) d) (seq (length (concat pre)) (length x)) = x.
Proof.
intros A pre x r d; rewrite map_seq_shift.
transitivity (map (fun j => nth j x d) (seq 0 (length x))).
- apply map_ext_in; intros j I; apply in_seq in I; apply nth_concat_block; lia.
- rewrite (@map_nth_prefix _ x d (length x)) by lia; apply firstn_all.
Qed.

Lemma key_block :
  forall (A B : Type) (f : A -> B) (pre : list (list A)) x r (d : A) dv,
    map (fun i => nth i (map f (concat (pre ++ x :: r))) dv) (seq (length (concat pre)) (length x)) = map f x.
Proof.
intros A B f pre x r d dv; rewrite map_seq_shift.
transitivity (map (fun j => f (nth j x d)) (seq 0 (length x))).
- apply map_ext_in; intros j I; apply in_seq in I.
  rewrite (nth_indep _ dv (f d)) by (rewrite map_length, concat_app, app_length; simpl; rewrite app_length; lia).
  rewrite map_nth, nth_concat_block by lia; reflexivity.
- rewrite <- (map_map (fun j => nth j x d) f), (@map_nth_prefix _ x d (length x)) by lia.
  rewrite firstn_all; reflexivity.
Qed.

Definition ev ce env (e : sexpr) (t : tuple T) := eval_sexpr ORN O basesort instance ce (slice_t T relname t :: env) e.

Lemma row_vals_sets :
  forall ce env ss t, row_vals_of ORN O basesort instance ce env (G_Sets ss) t = map (fun e => ev ce env e t) (concat ss).
Proof.
intros ce env ss t; unfold row_vals_of; induction ss as [ | x ss IH]; [reflexivity | ].
simpl; rewrite IH, map_app; reflexivity.
Qed.

Lemma gkeys_sets :
  forall ce env ss t, gkeys_of ORN O basesort instance ce env (G_Sets ss) t = map (fun e => ev ce env e t) (concat ss).
Proof.
intros ce env ss t; unfold gkeys_of; induction ss as [ | x ss IH]; [reflexivity | ].
simpl; rewrite IH, map_app; reflexivity.
Qed.

Lemma sets_groupings_spec :
  forall ce env (rows : list (tuple T)) pre r,
    set_groupings O (fun t => map (fun e => ev ce env e t) (concat (pre ++ r))) (concat (pre ++ r))
                  ((fix go (off : nat) (ss : list (list sexpr)) : list (list nat) :=
                      match ss with
                      | nil => nil
                      | l :: r => seq off (List.length l) :: go (off + List.length l)%nat r
                      end) (length (concat pre)) r) rows =
    flat_map (fun x =>
                let hid := sdedup nil (filter (fun e => negb (existsb (sexpr_eqb e) x)) (concat (pre ++ r))) in
                map (fun grp => (grp, hid))
                    (match x with
                     | nil => rows :: nil
                     | _ => group_on O (fun t => map (fun e => ev ce env e t) x) rows
                     end)) r.
Proof.
intros ce env rows pre r; revert pre; induction r as [ | x r IH]; intro pre; [reflexivity | ].
unfold set_groupings in *; cbn [flat_map]; f_equal.
- rewrite (@block_of_positions _ pre x r (E_Const T relname (null O))).
  destruct x as [ | y x]; [reflexivity | ].
  cbn zeta; f_equal; apply group_on_ext; intro t.
  exact (@key_block _ _ (fun e => ev ce env e t) pre (y :: x) r y _).
- replace (length (concat pre) + length x) with (length (concat (pre ++ x :: nil))) by
    (rewrite concat_app, app_length; simpl; rewrite app_nil_r; reflexivity).
  replace (pre ++ x :: r) with ((pre ++ x :: nil) ++ r) by (rewrite <- app_assoc; reflexivity).
  apply IH.
Qed.

Lemma set_groupings_ext :
  forall (rv1 rv2 : tuple T -> list (value T)) (univ : list sexpr) (positions : list (list nat)) (rows : list (tuple T)),
    (forall t, rv1 t = rv2 t) ->
    set_groupings O rv1 univ positions rows = set_groupings O rv2 univ positions rows.
Proof.
intros rv1 rv2 univ positions rows H; unfold set_groupings; apply flat_map_ext_in'; intros pos _.
cbn zeta; f_equal; destruct pos as [ | i pos]; [reflexivity | ].
apply group_on_ext; intro t; rewrite H; reflexivity.
Qed.

Lemma rollup_key_errors :
  forall ce env l t,
    existsb (is_error O) (gkeys_of ORN O basesort instance ce env (G_Sets (rollup_sets l)) t) =
    existsb (is_error O) (gkeys_of ORN O basesort instance ce env (G_Rollup l) t).
Proof.
intros ce env l t; rewrite gkeys_sets; destruct (concat_rollup l) as [rest [E R]]; rewrite E.
change (gkeys_of ORN O basesort instance ce env (G_Rollup l) t) with (map (fun e => ev ce env e t) l).
rewrite map_app, existsb_app.
case_eq (existsb (is_error O) (map (fun e => ev ce env e t) l)); intro K; [reflexivity | ].
simpl; case_eq (existsb (is_error O) (map (fun e => ev ce env e t) rest)); intro K'; [ | reflexivity].
apply existsb_exists in K'; destruct K' as [v [Iv Ev]]; apply in_map_iff in Iv; destruct Iv as [y [Ey Iy]].
assert (K'' : existsb (is_error O) (map (fun e => ev ce env e t) l) = true).
{ apply existsb_exists; exists v; split; [ | exact Ev].
  rewrite <- Ey; apply (in_map (fun e => ev ce env e t)); apply R; exact Iy. }
rewrite K'' in K; discriminate K.
Qed.

Theorem rollup_as_grouping_sets :
  forall ce env sq s lf w l h ex,
    (forall e, In e l -> sexpr_eqb e e = true) ->
    eval_sspec ORN O basesort instance ce env (Select sq s lf w (G_Rollup l) h) ex =
    eval_sspec ORN O basesort instance ce env (Select sq s lf w (G_Sets (rollup_sets l)) h) ex.
Proof.
intros ce env sq s lf w l h ex Hrefl; rewrite !eval_select; cbv zeta; f_equal.
unfold grouping_part; cbv zeta iota beta.
rewrite (map_ext _ _ (fun t => f_equal (fun b : bool => if b then err_row O t else t) (rollup_key_errors ce env l t))).
set (R := map _ (where_rows ORN O basesort instance ce env lf w)).
change (set_groupings O (fun t => map (fun e => ev ce env e t) l) l (rollup_sets (seq 0 (length l))) R =
        set_groupings O (row_vals_of ORN O basesort instance ce env (G_Sets (rollup_sets l))) (concat (rollup_sets l))
          ((fix go (off : nat) (ss : list (list sexpr)) : list (list nat) :=
              match ss with
              | nil => nil
              | l :: r => seq off (List.length l) :: go (off + List.length l)%nat r
              end) 0 (rollup_sets l)) R).
rewrite (set_groupings_ext (row_vals_of ORN O basesort instance ce env (G_Sets (rollup_sets l)))
           (fun t => map (fun e => ev ce env e t) (concat (rollup_sets l)))) by (intro t; apply row_vals_sets).
rewrite (rollup_groupings T O relname (ev ce env) l R).
change (concat (rollup_sets l)) with (concat (nil ++ rollup_sets l)).
change 0 with (length (concat (@nil (list sexpr)))).
rewrite (sets_groupings_spec ce env R nil (rollup_sets l)); simpl app.
simpl length.
match goal with |- flat_map ?F _ = flat_map ?G _ =>
  transitivity (flat_map (fun k => G (firstn k l)) (rev (seq 0 (S (length l)))));
  [ | unfold rollup_sets; rewrite flat_map_map'; reflexivity] end.
apply flat_map_ext_in'; intros k I; rewrite <- in_rev, in_seq in I.
cbn zeta beta.
assert (Hh : forall P, sdedup nil (filter P (concat (rollup_sets l))) = sdedup nil (filter P l)).
{ intro P; destruct (concat_rollup l) as [rest [E R']]; rewrite E, filter_app.
  apply sdedup_app.
  + intros y Iy; apply filter_In in Iy; destruct Iy as [Iy Py]; split; [apply Hrefl, R'; exact Iy | ].
    right; apply filter_In; split; [apply R'; exact Iy | exact Py].
  + intros y Iy; apply filter_In in Iy; apply Hrefl; tauto. }
rewrite Hh; f_equal.
destruct k as [ | k]; [reflexivity | ].
destruct l as [ | a l]; [simpl in I; lia | reflexivity].
Qed.

End RollupRows.
