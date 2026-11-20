(** * The oracles of the logic-bug detection tools, justified by three-valued logic (TODO 5.8)

    TLP (ternary logic partitioning, used by SQLancer, and by ValScope and Pinolo for the MySQL family):
    the rows of a query are, as a bag, the rows where [p] is true, those where [NOT p] is true and those
    where [p] is unknown ([p IS NULL]). [WHERE] keeps the rows whose condition is true, so the three
    filtered queries partition the unfiltered one. NoREC: the number of rows where [p] is true is the sum
    over all the rows of [CASE WHEN p THEN 1 ELSE 0 END]. *)
Require Import List Permutation Arith ZArith Lia.
Require Import Bool3.
Import ListNotations.

Definition b3_true (b : bool3) : bool := match b with true3 => true | _ => false end.
Definition b3_unknown (b : bool3) : bool := match b with unknown3 => true | _ => false end.

(** [NOT p] is true exactly when [p] is false *)
Lemma negb3_true : forall b, b3_true (negb3 b) = match b with false3 => true | _ => false end.
Proof. intros [ | | ]; reflexivity. Qed.

(** TLP *)
Theorem tlp_partition :
  forall (A : Type) (p : A -> bool3) (l : list A),
    Permutation l
      (filter (fun x => b3_true (p x)) l ++ filter (fun x => b3_true (negb3 (p x))) l
       ++ filter (fun x => b3_unknown (p x)) l).
Proof.
  intros A p l; induction l as [ | a l IH]; simpl; [constructor | ].
  destruct (p a); simpl.
  - constructor; exact IH.
  - apply Permutation_cons_app; exact IH.
  - rewrite app_assoc; apply Permutation_cons_app; rewrite <- app_assoc; exact IH.
Qed.

(** TLP for an aggregate which is a sum ([COUNT], [SUM] of non-negative values): the sum over the rows
    is the sum of the three partitions *)
Theorem tlp_sum :
  forall (A : Type) (p : A -> bool3) (v : A -> nat) (l : list A),
    fold_right plus 0 (map v l) =
    fold_right plus 0 (map v (filter (fun x => b3_true (p x)) l)) +
    fold_right plus 0 (map v (filter (fun x => b3_true (negb3 (p x))) l)) +
    fold_right plus 0 (map v (filter (fun x => b3_unknown (p x)) l)).
Proof.
  intros A p v l; induction l as [ | a l IH]; simpl; [reflexivity | ].
  destruct (p a); simpl; rewrite IH; ring.
Qed.

(** NoREC *)
Theorem norec :
  forall (A : Type) (p : A -> bool3) (l : list A),
    length (filter (fun x => b3_true (p x)) l) =
    fold_right plus 0 (map (fun x => if b3_true (p x) then 1 else 0) l).
Proof.
  intros A p l; induction l as [ | a l IH]; simpl; [reflexivity | ].
  destruct (b3_true (p a)); simpl; rewrite IH; reflexivity.
Qed.

(** * ValScope's value rules (TODO 5.8)

    ValScope combines the containment of the rows of two queries (set semantics: a stronger [WHERE] keeps a
    subset of the rows, [containment_and] and [containment_or] of [SqlFullFacts.v] state it as a filter of the
    rows) with the values of their aggregates (value semantics): over a filtered subset of the rows, [COUNT]
    and a [SUM] of non-negative values do not grow, [MAX] does not grow and [MIN] does not shrink (when the
    subset is not empty). A query pair which breaks one of these relations shows a bug. *)

Lemma count_filter_le : forall (A : Type) (f : A -> bool) (l : list A), length (filter f l) <= length l.
Proof.
intros A f l; induction l as [ | a l IH]; simpl; [lia | destruct (f a); simpl; lia].
Qed.

Lemma sum_filter_le :
  forall (A : Type) (f : A -> bool) (v : A -> Z) (l : list A), (forall x, In x l -> (0 <= v x)%Z) ->
    (fold_right Z.add 0 (map v (filter f l)) <= fold_right Z.add 0 (map v l))%Z.
Proof.
intros A f v l H; induction l as [ | a l IH]; simpl; [lia | ].
assert (Ha := H a (or_introl eq_refl)); assert (IH' := IH (fun x K => H x (or_intror K))).
destruct (f a); simpl; lia.
Qed.

(** the maximum and the minimum of a non-empty list *)
Definition zmax (l : list Z) : option Z :=
  match l with nil => None | x :: r => Some (fold_left Z.max r x) end.
Definition zmin (l : list Z) : option Z :=
  match l with nil => None | x :: r => Some (fold_left Z.min r x) end.

Lemma fold_max_ge : forall r x y, In y (x :: r) -> (y <= fold_left Z.max r x)%Z.
Proof.
intro r; induction r as [ | z r IH]; intros x y H; simpl in *.
- destruct H as [H | H]; [subst; lia | contradiction].
- destruct H as [H | [H | H]].
  + subst; apply Z.le_trans with (Z.max y z); [lia | apply IH; left; reflexivity].
  + subst; apply Z.le_trans with (Z.max x y); [lia | apply IH; left; reflexivity].
  + apply IH; right; exact H.
Qed.

Lemma fold_max_in : forall r x, In (fold_left Z.max r x) (x :: r).
Proof.
intro r; induction r as [ | z r IH]; intro x; simpl; [left; reflexivity | ].
destruct (IH (Z.max x z)) as [H | H].
- rewrite <- H; destruct (Z.max_spec x z) as [[_ K] | [_ K]]; rewrite K; [right; left | left]; reflexivity.
- right; right; exact H.
Qed.

Lemma fold_min_le : forall r x y, In y (x :: r) -> (fold_left Z.min r x <= y)%Z.
Proof.
intro r; induction r as [ | z r IH]; intros x y H; simpl in *.
- destruct H as [H | H]; [subst; lia | contradiction].
- destruct H as [H | [H | H]].
  + subst; apply Z.le_trans with (Z.min y z); [apply IH; left; reflexivity | lia].
  + subst; apply Z.le_trans with (Z.min x y); [apply IH; left; reflexivity | lia].
  + apply IH; right; exact H.
Qed.

Lemma fold_min_in : forall r x, In (fold_left Z.min r x) (x :: r).
Proof.
intro r; induction r as [ | z r IH]; intro x; simpl; [left; reflexivity | ].
destruct (IH (Z.min x z)) as [H | H].
- rewrite <- H; destruct (Z.min_spec x z) as [[_ K] | [_ K]]; rewrite K; [left | right; left]; reflexivity.
- right; right; exact H.
Qed.

Theorem max_filter_le :
  forall (A : Type) (f : A -> bool) (v : A -> Z) (l : list A) m m',
    zmax (map v (filter f l)) = Some m -> zmax (map v l) = Some m' -> (m <= m')%Z.
Proof.
intros A f v l m m' H H'.
destruct (map v (filter f l)) as [ | x r] eqn:E; [discriminate H | injection H; intros <-].
destruct (map v l) as [ | y q] eqn:E'; [discriminate H' | injection H'; intros <-].
assert (I := fold_max_in r x); rewrite <- E in I.
apply in_map_iff in I; destruct I as [a [Ha Ia]]; apply filter_In in Ia.
apply fold_max_ge; rewrite <- E', <- Ha; apply in_map; tauto.
Qed.

Theorem min_filter_ge :
  forall (A : Type) (f : A -> bool) (v : A -> Z) (l : list A) m m',
    zmin (map v (filter f l)) = Some m -> zmin (map v l) = Some m' -> (m' <= m)%Z.
Proof.
intros A f v l m m' H H'.
destruct (map v (filter f l)) as [ | x r] eqn:E; [discriminate H | injection H; intros <-].
destruct (map v l) as [ | y q] eqn:E'; [discriminate H' | injection H'; intros <-].
assert (I := fold_min_in r x); rewrite <- E in I.
apply in_map_iff in I; destruct I as [a [Ha Ia]]; apply filter_In in Ia.
apply fold_min_le; rewrite <- E', <- Ha; apply in_map; tauto.
Qed.
