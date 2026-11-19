(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**                      Some properties of the semantics of SqlFull                *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

Require Import List Bool NArith.

Require Import BasicFacts ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection 
        FlatData Bool3 Formula SqlFull.

Section Sec.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.
Hypothesis ORN : Oset.Rcd relname.
Hypothesis O : dialect T.

Import Tuple.

Notation setA := (Fset.set (A T)).
Notation tuple := (tuple T).
Notation BTupleT := (Fecol.CBag (CTuple T)).
Notation bagT := (Febag.bag BTupleT).

Hypothesis basesort : relname -> setA.
Hypothesis instance : relname -> bagT.

Notation eval_sexpr := (eval_sexpr ORN O basesort instance).
Notation eval_scond := (eval_scond ORN O basesort instance).
Notation eval_squery := (eval_squery ORN O basesort instance).
Notation eval_sfrom := (eval_sfrom ORN O basesort instance).
Notation eval_sspec := (eval_sspec ORN O basesort instance).

(** * Sorting *)

Lemma stable_sort_trivial :
  forall (X : Type) (le : X -> X -> bool) (l : list X),
    (forall x y, le x y = true) -> stable_sort le l = l.
Proof.
intros X le l H; induction l as [ | x l]; [apply refl_equal | ].
unfold stable_sort in *; simpl; rewrite IHl.
destruct l as [ | y l]; [apply refl_equal | ].
simpl; rewrite H; apply refl_equal.
Qed.

Lemma sort_on_nil :
  forall (X : Type) (keys : X -> list (value T)) (l : list X), sort_on O nil keys l = l.
Proof.
intros X keys l; unfold sort_on.
rewrite stable_sort_trivial; [ | intros; apply refl_equal].
rewrite map_map; simpl; apply map_id; intros; apply refl_equal.
Qed.

Lemma eval_order_unfold :
  forall ce env q lo off lim,
    eval_squery ce env (SQ_Order q lo off lim) =
    let rows := 
        match q with
        | SQ_Select sp => eval_sspec ce env sp (map (fun o => match o with O_By e _ _ => e end) lo)
        | _ => map (fun t => (t, slice_t T t :: env)) (eval_squery ce env q)
        end in
    let keys (x : tuple * senv T) :=
        map (fun o => match o with
                      | O_By e _ _ => 
                        match is_output_col (fst x) e with
                        | Some v => v
                        | None => eval_sexpr ce (snd x) e
                        end
                      end) lo in
    map (@fst _ _) (offset_limit off lim (sort_on O (map (@sorder_spec _ _) lo) keys rows)).
Proof.
intros ce env q lo off lim; destruct q; apply refl_equal.
Qed.

(** A query without ORDER BY, OFFSET nor LIMIT. *)
Theorem order_by_nothing :
  forall ce env q, eval_squery ce env (SQ_Order q nil None None) = eval_squery ce env q.
Proof.
intros ce env q; rewrite eval_order_unfold; cbv zeta; unfold offset_limit.
simpl map at 2; rewrite sort_on_nil.
destruct q; try (rewrite map_map; simpl; apply map_id; intros; apply refl_equal).
apply refl_equal.
Qed.

(** * Joins *)

(** An inner join is the selection, by its condition, of a cross product. *)
Lemma inner_join_is_filter :
  forall s1 s2 (l1 l2 : list tuple) on,
    eval_join T J_Inner s1 s2 l1 (fun _ => l2) l2 on = filter on (cross_product T l1 l2).
Proof.
intros s1 s2 l1 l2 on; unfold eval_join, cross_product.
induction l1 as [ | t1 l1]; [apply refl_equal | ].
simpl; rewrite filter_app, IHl1; apply refl_equal.
Qed.

Lemma filter_true :
  forall (X : Type) (f : X -> bool) (l : list X), (forall x, f x = true) -> filter f l = l.
Proof.
intros X f l H; induction l as [ | x l]; [apply refl_equal | ].
simpl; rewrite H, IHl; apply refl_equal.
Qed.

Theorem inner_join_spec :
  forall ce env f1 f2 c,
    eval_sfrom ce env (Fr_Join J_Inner false f1 f2 c) =
    filter (fun t => is_true3 T (eval_scond ce (slice_t T t :: env) c))
           (cross_product T (eval_sfrom ce env f1) (eval_sfrom ce env f2)).
Proof.
intros ce env f1 f2 c.
exact (inner_join_is_filter (sfrom_sort ORN basesort ce f1) (sfrom_sort ORN basesort ce f2) _ _ _).
Qed.

Theorem cross_join_spec :
  forall ce env f1 f2,
    eval_sfrom ce env (Fr_Cross f1 f2) =
    cross_product T (eval_sfrom ce env f1) (eval_sfrom ce env f2).
Proof.
intros ce env f1 f2; unfold Fr_Cross; rewrite inner_join_spec.
apply filter_true.
intro t; change (is_true3 T (Bool.true (B T)) = true).
unfold is_true3; rewrite Bool.true_is_true; apply refl_equal.
Qed.

(** The rows of a left join which are not padded with NULLs are those of the
    inner join: a left join without unmatched row is an inner join. *)
Lemma left_join_no_padding :
  forall s1 s2 (l1 l2 : list tuple) on,
    (forall t1, In t1 l1 -> filter on (map (join_tuple T t1) l2) <> nil) ->
    eval_join T J_Left s1 s2 l1 (fun _ => l2) l2 on =
    eval_join T J_Inner s1 s2 l1 (fun _ => l2) l2 on.
Proof.
intros s1 s2 l1 l2 on; unfold eval_join.
induction l1 as [ | t1 l1]; intro H; [apply refl_equal | ].
simpl; rewrite IHl1; [ | intros; apply H; right; assumption].
apply f_equal2; [ | apply refl_equal].
assert (H1 := H t1 (or_introl _ (refl_equal _))).
destruct (filter on (map (join_tuple T t1) l2)); [apply False_rec; apply H1 | ]; apply refl_equal.
Qed.

(** * Conditions: the connectives are those of the logic of [B T] *)

Lemma eval_not_not :
  forall ce env c, eval_scond ce env (C_Not (C_Not c)) = eval_scond ce env c.
Proof.
intros ce env c; exact (Bool.negb_negb (B T) (eval_scond ce env c)).
Qed.

Lemma eval_de_morgan :
  forall ce env c1 c2, 
    eval_scond ce env (C_Not (C_Conj And_F c1 c2)) = 
    eval_scond ce env (C_Conj Or_F (C_Not c1) (C_Not c2)).
Proof.
intros ce env c1 c2; exact (Bool.negb_andb (B T) (eval_scond ce env c1) (eval_scond ce env c2)).
Qed.

Lemma eval_and_comm :
  forall ce env c1 c2, 
    eval_scond ce env (C_Conj And_F c1 c2) = eval_scond ce env (C_Conj And_F c2 c1).
Proof.
intros ce env c1 c2; exact (Bool.andb_comm (B T) (eval_scond ce env c1) (eval_scond ce env c2)).
Qed.

(** * Expressions *)

(** CASE evaluates only one of its branches. *)
Lemma eval_case_true :
  forall ce env c e1 e2,
    is_true3 T (eval_scond ce env c) = true ->
    eval_sexpr ce env (E_Case c e1 e2) = eval_sexpr ce env e1.
Proof.
intros ce env c e1 e2 H.
change ((if is_true3 T (eval_scond ce env c) then eval_sexpr ce env e1 else eval_sexpr ce env e2) =
        eval_sexpr ce env e1).
rewrite H; apply refl_equal.
Qed.

Lemma eval_case_not_true :
  forall ce env c e1 e2,
    is_true3 T (eval_scond ce env c) = false ->
    eval_sexpr ce env (E_Case c e1 e2) = eval_sexpr ce env e2.
Proof.
intros ce env c e1 e2 H.
change ((if is_true3 T (eval_scond ce env c) then eval_sexpr ce env e1 else eval_sexpr ce env e2) =
        eval_sexpr ce env e2).
rewrite H; apply refl_equal.
Qed.

(** An aggregate of the current block, without DISTINCT nor FILTER, is the
    aggregate of the values of its argument on the tuples of the group. *)
Lemma eval_agg_group :
  forall ce env sa g ag a,
    a inS sa ->
    eval_sexpr ce ((sa, g) :: env) (E_Agg ag Set_All (E_Col T relname a) (C_True T relname)) =
    interp_aggregate T ag (map (fun t => dot T t a) g).
Proof.
intros ce env sa g ag a Ha.
change (interp_aggregate T ag
          (match agg_env (a :: nil) ((sa, g) :: env) with
           | nil => nil
           | (sa', g') :: env' =>
             map (fun t => lookup ((sa', t :: nil) :: env') a)
                 (filter (fun t => is_true3 T (Bool.true (B T))) g')
           end) = interp_aggregate T ag (map (fun t => dot T t a) g)).
unfold agg_env; simpl; rewrite Ha; simpl.
apply f_equal.
rewrite filter_true.
- rewrite <- map_eq; intros t Ht; rewrite Ha; apply refl_equal.
- intro t; unfold is_true3; rewrite Bool.true_is_true; apply refl_equal.
Qed.

(** * Set operations *)

Lemma union_all_spec :
  forall ce env q1 q2,
    Fset.equal (A T) (squery_sort ORN basesort ce q1) (squery_sort ORN basesort ce q2) = true ->
    eval_squery ce env (SQ_Set Union Set_All q1 q2) = 
    eval_squery ce env q1 ++ eval_squery ce env q2.
Proof.
intros ce env q1 q2 H.
change ((if Fset.equal (A T) (squery_sort ORN basesort ce q1) (squery_sort ORN basesort ce q2)
         then eval_set_op O Union Set_All (eval_squery ce env q1) (eval_squery ce env q2)
         else nil) = eval_squery ce env q1 ++ eval_squery ce env q2).
rewrite H; apply refl_equal.
Qed.

End Sec.
