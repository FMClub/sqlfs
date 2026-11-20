(** * The oracles of the logic-bug detection tools, justified by three-valued logic (TODO 5.8)

    TLP (ternary logic partitioning, used by SQLancer, and by ValScope and Pinolo for the MySQL family):
    the rows of a query are, as a bag, the rows where [p] is true, those where [NOT p] is true and those
    where [p] is unknown ([p IS NULL]). [WHERE] keeps the rows whose condition is true, so the three
    filtered queries partition the unfiltered one. NoREC: the number of rows where [p] is true is the sum
    over all the rows of [CASE WHEN p THEN 1 ELSE 0 END]. *)
Require Import List Permutation Arith.
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
