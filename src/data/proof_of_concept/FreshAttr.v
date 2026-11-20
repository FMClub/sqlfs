
From Coq Require Import String.
From Coq Require Decimal DecimalNat DecimalString DecimalFacts List.
From Coq Require Import Arith Lia.

Require Import Mem OrderedSet.
Require Import FTuples GenericInstance.

Import List.ListNotations.

Open Scope string_scope.
Open Scope list_scope.



Definition nat_to_str (n : nat) : string :=
    let u := Decimal.rev (DecimalNat.Unsigned.to_lu n) in
    DecimalString.NilZero.string_of_uint u.


Definition create_name (name : string) (n : nat) :=
    String.append name (nat_to_str n).


Definition name_in_list (s : string) (l : list string) : bool :=
    Mem.mem_bool eqb s l.


Section Gen_name.

  Variable name : string.

  Variable name_list : list string.

  Fixpoint gen_name_aux (n : nat) (count : nat) : string
     := let new_name := create_name name n in
        match count with
        | 0 => new_name
        | S count' => 
            if name_in_list new_name name_list then
                 gen_name_aux (S n) count'
            else new_name
        end.

  Definition gen_name : string
        := gen_name_aux 0 (S (Datatypes.length name_list)).

End Gen_name.


Example gen_name_ex1: 
   gen_name "x" [ "x3"; "y0"; "x1"; "x4"; "x0"; "x2" ] = "x5".
Proof. reflexivity. Qed.



Definition name_of_attribute (a : attribute) : string
    := match a with
       | Attr_string name
       | Attr_Z name
       | Attr_bool name
       | Attr_Q name => name
       end.

Definition names_of_attributes (l : list attribute) : list string
     := List.map name_of_attribute l.


Definition fresh_attr (a : attribute) (l : list attribute) : attribute
   := let name := gen_name (name_of_attribute a) (names_of_attributes l) in
      match a with
      | Attr_string _ => Attr_string name
      | Attr_Z _ => Attr_Z name
      | Attr_bool _ => Attr_bool name
      | Attr_Q _ => Attr_Q name
      end.


(** * Freshness

    [gen_name] tries [name0], [name1], ...: it returns a name of the list only if all the
    [length l + 2] names it tried are in [l]; they are pairwise distinct (the decimal
    printing of the naturals is injective), so the list would have more than [length l]
    distinct elements. *)

Lemma to_lu_not_nil : forall n, DecimalNat.Unsigned.to_lu n <> Decimal.Nil.
Proof.
  intros [|n]; simpl; [discriminate|].
  generalize (DecimalNat.Unsigned.to_lu n); intros d; destruct d; simpl; discriminate.
Qed.

Lemma nat_to_str_inj : forall n m, nat_to_str n = nat_to_str m -> n = m.
Proof.
  intros n m H; unfold nat_to_str in H.
  assert (Hn : Decimal.rev (DecimalNat.Unsigned.to_lu n) <> Decimal.Nil).
  { intro K; apply DecimalFacts.rev_nil_inv in K; exact (to_lu_not_nil n K). }
  assert (Hm : Decimal.rev (DecimalNat.Unsigned.to_lu m) <> Decimal.Nil).
  { intro K; apply DecimalFacts.rev_nil_inv in K; exact (to_lu_not_nil m K). }
  apply (f_equal DecimalString.NilZero.uint_of_string) in H.
  rewrite (DecimalString.NilZero.usu _ Hn), (DecimalString.NilZero.usu _ Hm) in H.
  injection H; intro K.
  apply (f_equal Decimal.rev) in K; rewrite !DecimalFacts.rev_rev in K.
  rewrite <- (DecimalNat.Unsigned.of_to_lu n), <- (DecimalNat.Unsigned.of_to_lu m), K; reflexivity.
Qed.

Lemma append_inj : forall p a b, String.append p a = String.append p b -> a = b.
Proof.
  induction p as [|c p IH]; simpl; intros a b H; [exact H|].
  injection H; apply IH.
Qed.

Lemma create_name_inj : forall name n m, create_name name n = create_name name m -> n = m.
Proof. intros name n m H; apply nat_to_str_inj, (append_inj name), H. Qed.

Lemma name_in_list_true : forall s l, name_in_list s l = true -> List.In s l.
Proof.
  intros s l H; unfold name_in_list in H; rewrite Mem.mem_bool_true_iff in H.
  destruct H as [s' [H1 H2]]; apply String.eqb_eq in H1; subst; exact H2.
Qed.

Lemma gen_name_aux_in : forall name l c n,
    List.In (gen_name_aux name l n c) l ->
    forall k, n <= k <= n + c -> List.In (create_name name k) l.
Proof.
  intros name l; induction c as [|c IH]; intros n H k Hk; simpl in H.
  - replace k with n by lia; exact H.
  - case_eq (name_in_list (create_name name n) l); intro E; rewrite E in H.
    + destruct (PeanoNat.Nat.eq_dec k n) as [->|D].
      * apply name_in_list_true, E.
      * apply (IH (S n) H); lia.
    + exfalso.
      revert E; unfold name_in_list; rewrite <- Bool.not_true_iff_false; intro E; apply E.
      rewrite Mem.mem_bool_true_iff; exists (create_name name n); split; [apply String.eqb_refl | exact H].
Qed.

Lemma NoDup_map_inj : forall (A B : Type) (f : A -> B) l,
    (forall x y, f x = f y -> x = y) -> List.NoDup l -> List.NoDup (List.map f l).
Proof.
  intros A B f l Hf; induction 1 as [|x l Hx Hl IH]; simpl; constructor; [|exact IH].
  intro K; apply List.in_map_iff in K; destruct K as [y [Ey Hy]].
  apply Hf in Ey; subst; contradiction.
Qed.

Lemma gen_name_fresh : forall name l, ~ List.In (gen_name name l) l.
Proof.
  intros name l H; unfold gen_name in H.
  assert (Inc : List.incl (List.map (create_name name) (List.seq 0 (S (S (Datatypes.length l))))) l).
  { intros x Hx; apply List.in_map_iff in Hx; destruct Hx as [k [<- Hk]].
    apply List.in_seq in Hk; apply (gen_name_aux_in _ _ _ _ H); lia. }
  apply List.NoDup_incl_length in Inc.
  - rewrite List.map_length, List.seq_length in Inc; lia.
  - apply NoDup_map_inj; [apply create_name_inj | apply List.seq_NoDup].
Qed.

Lemma fresh_attr_is_fresh : forall a s,
     Oset.mem_bool OAN (fresh_attr a s) s = false.
Proof.
  intros a s.
  rewrite <- Bool.not_true_iff_false, Oset.mem_bool_true_iff; intro H.
  apply (gen_name_fresh (name_of_attribute a) (names_of_attributes s)).
  unfold names_of_attributes; apply List.in_map_iff.
  exists (fresh_attr a s); split; [|exact H].
  destruct a; reflexivity.
Qed.









