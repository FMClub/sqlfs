(** * Renaming the columns of the queries of the dialects

    [eval_rename] ([SqlRename.v]) for the instance of the dialects: a bijection of the names of the attributes
    which keeps the name of the attribute of the failed rows renames the rows of every query ([eval_rename_names]);
    the exchange of two names is such a bijection ([swap_name]). The tuples of the instance are association
    lists, so that a missing attribute has the default value of its type ([td_dot]). *)
Require Import List String Bool.
Require Import BasicFacts ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection FlatData SqlFull SqlRename
        Values TuplesImpl GenericInstance Dialects.
Import Tuple.

Section Sec.

Variable d : vsem.
Notation T := (TD d).

Lemma td_dot : forall (t : tuple T) (a : attribute T),
  (a inS? labels T t) = false -> dot T t a = default_value T (type_of_attribute T a).
Proof.
intros t a H; cbn [TD Tuple2.T dot labels type_of_attribute default_value A] in *.
unfold Tuple2.dot; unfold Tuple2.support in H.
case_eq (Oset.find OAN a t); [ | intros; reflexivity].
intros v Hv; apply Oset.find_some in Hv.
rewrite Fset.mem_mk_set in H; rewrite <- Bool.not_true_iff_false in H; elim H.
rewrite Oset.mem_bool_true_iff, in_map_iff; exists (a, v); split; [reflexivity | exact Hv].
Qed.

(** the attribute of the same type, with the name [f s] *)
Definition rename_names (f : string -> string) (a : GenericInstance.attribute) : GenericInstance.attribute :=
  match a with
  | Attr_string s => Attr_string (f s)
  | Attr_Z s => Attr_Z (f s)
  | Attr_bool s => Attr_bool (f s)
  | Attr_Q s => Attr_Q (f s)
  end.

Variables f g : string -> string.
Hypothesis Hgf : forall s, g (f s) = s.
Hypothesis Hfg : forall s, f (g s) = s.
Hypothesis Herr : f "#error" = "#error".

Variable relname : Type.
Variable ORN : Oset.Rcd relname.
Variables basesort basesort' : relname -> Fset.set (A T).
Variables instance instance' : relname -> Febag.bag (Fecol.CBag (CTuple T)).
Hypothesis Hbs : forall r, basesort' r =S= rs T (rename_names f) (basesort r).
Hypothesis Hinst : forall r, RL T (rename_names f) (rename_names g)
                               (Febag.elements _ (instance' r)) (Febag.elements _ (instance r)).

Theorem eval_rename_names : forall q : squery T relname,
  RL T (rename_names f) (rename_names g)
     (eval_query_list ORN (dialect_of d) basesort' instance' (r_q T relname (rename_names f) q))
     (eval_query_list ORN (dialect_of d) basesort instance q).
Proof.
apply eval_rename; trivial.
- intros [s | s | s | s]; simpl; rewrite Hgf; reflexivity.
- intros [s | s | s | s]; simpl; rewrite Hfg; reflexivity.
- intros [s | s | s | s]; reflexivity.
- apply td_dot.
- intros [s | s | s | s]; reflexivity.
- simpl; rewrite Herr; reflexivity.
Qed.

End Sec.

(** the exchange of two names *)
Definition swap_name (x y s : string) : string :=
  if String.eqb s x then y else if String.eqb s y then x else s.

Lemma swap_name_invol : forall x y s, swap_name x y (swap_name x y s) = s.
Proof.
intros x y s; unfold swap_name.
destruct (String.eqb_spec s x) as [E | N].
- subst s; destruct (String.eqb_spec y x) as [E | N]; [exact E | rewrite String.eqb_refl; reflexivity].
- destruct (String.eqb_spec s y) as [E | N'].
  + subst s; rewrite String.eqb_refl; reflexivity.
  + destruct (String.eqb_spec s x); [contradiction | ]; destruct (String.eqb_spec s y); [contradiction | reflexivity].
Qed.
