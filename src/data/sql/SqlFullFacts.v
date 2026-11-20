(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**                      Some properties of the semantics of SqlFull                *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

Require Import List Bool NArith String Permutation Lia.

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
Notation scond_raises := (scond_raises ORN O basesort instance).

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

(** ** The merge sort is the insertion sort for a total preorder (TODO 6.6)

    On elements where [le] is total and transitive (a property [P] of the elements), the stable merge sort
    [msort] and the stable insertion sort [stable_sort] give the same list. *)
Section Msort.

Variable X : Type.
Variable le : X -> X -> bool.
Variable P : X -> Prop.
Hypothesis Htot : forall x y, P x -> P y -> le x y = true \/ le y x = true.
Hypothesis Htrans : forall x y z, P x -> P y -> P z -> le x y = true -> le y z = true -> le x z = true.

Lemma merge_nil_r : forall l, merge le l nil = l.
Proof. intros [ | x l]; reflexivity. Qed.

Lemma merge_nil_l : forall l, merge le nil l = l.
Proof. intros [ | x l]; reflexivity. Qed.

Lemma merge_cons_cons :
  forall x l1 y l2,
    merge le (x :: l1) (y :: l2) =
    if le x y then x :: merge le l1 (y :: l2) else y :: merge le (x :: l1) l2.
Proof. intros; reflexivity. Qed.

Lemma insert_merge :
  forall sa sb x, Forall P sa -> Forall P sb -> P x ->
    insert_sorted le x (merge le sa sb) = merge le (insert_sorted le x sa) sb.
Proof.
intro sa; induction sa as [ | z sa IH]; intros sb x Ha Hb Hx.
- induction sb as [ | y sb IHb]; [reflexivity | ].
  change (merge le nil (y :: sb)) with (y :: sb); cbn [insert_sorted].
  rewrite merge_cons_cons; destruct (le x y); [reflexivity | ].
  f_equal; inversion Hb; subst; rewrite merge_nil_l in IHb; change (insert_sorted le x nil) with (x :: nil) in IHb; apply IHb; trivial.
- inversion Ha as [ | ? ? Hz Ha']; subst.
  induction sb as [ | y sb IHb]; [rewrite !merge_nil_r; reflexivity | ].
  inversion Hb as [ | ? ? Hy Hb']; subst.
  rewrite merge_cons_cons; cbn [insert_sorted].
  case_eq (le x z); intro Kxz; case_eq (le z y); intro Kzy.
  + cbn [insert_sorted]; rewrite Kxz, merge_cons_cons, (Htrans Hx Hz Hy Kxz Kzy), merge_cons_cons, Kzy.
    reflexivity.
  + cbn [insert_sorted]; rewrite merge_cons_cons.
    case_eq (le x y); intro Kxy.
    * rewrite merge_cons_cons, Kzy; reflexivity.
    * f_equal; rewrite IHb; trivial; cbn [insert_sorted]; rewrite Kxz; reflexivity.
  + cbn [insert_sorted]; rewrite Kxz, merge_cons_cons, Kzy, IH; trivial.
  + cbn [insert_sorted].
    assert (Kxy : le x y = false).
    { case_eq (le x y); intro Kxy; [ | reflexivity].
      destruct (Htot Hx Hz) as [K | K]; [rewrite K in Kxz; discriminate | ].
      rewrite (Htrans Hz Hx Hy K Kxy) in Kzy; discriminate. }
    rewrite Kxy, merge_cons_cons, Kzy; f_equal.
    rewrite IHb; trivial; cbn [insert_sorted]; rewrite Kxz; reflexivity.
Qed.

Lemma Forall_insert : forall x l, P x -> Forall P l -> Forall P (insert_sorted le x l).
Proof.
intros x l Hx Hl; induction Hl as [ | y l Hy Hl IH]; cbn [insert_sorted]; [constructor; auto | ].
destruct (le x y); constructor; auto.
Qed.

Lemma Forall_stable_sort : forall l, Forall P l -> Forall P (stable_sort le l).
Proof.
intros l Hl; induction Hl as [ | x l Hx Hl IH]; [constructor | ].
apply Forall_insert; trivial.
Qed.

Lemma stable_sort_app :
  forall a b, Forall P a -> Forall P b ->
    stable_sort le (a ++ b) = merge le (stable_sort le a) (stable_sort le b).
Proof.
intros a b Ha Hb; induction Ha as [ | x a Hx Ha IH]; [simpl; rewrite merge_nil_l; reflexivity | ].
change (insert_sorted le x (stable_sort le (a ++ b)) = merge le (insert_sorted le x (stable_sort le a)) (stable_sort le b)).
rewrite IH; apply insert_merge; trivial; apply Forall_stable_sort; trivial.
Qed.

Lemma msort_fuel_stable_sort :
  forall n l, (List.length l <= n)%nat -> Forall P l -> msort_fuel le n l = stable_sort le l.
Proof.
intro n; induction n as [ | n IH]; intros l Hn Hl.
- destruct l; [reflexivity | simpl in Hn; lia].
- destruct l as [ | x [ | y l]]; [reflexivity | reflexivity | ].
  set (k := x :: y :: l) in *.
  change (merge le (msort_fuel le n (firstn (PeanoNat.Nat.div (List.length k) 2) k))
                   (msort_fuel le n (skipn (PeanoNat.Nat.div (List.length k) 2) k)) = stable_sort le k).
  set (h := PeanoNat.Nat.div (List.length k) 2).
  assert (D := PeanoNat.Nat.div_mod (List.length k) 2 (ltac:(lia))).
  assert (M := PeanoNat.Nat.mod_upper_bound (List.length k) 2 (ltac:(lia))).
  assert (L : (2 <= List.length k)%nat) by (unfold k; simpl; lia).
  fold h in D.
  rewrite <- (firstn_skipn h k) in Hl; apply Forall_app in Hl; destruct Hl as [H1 H2].
  rewrite IH, IH; trivial.
  + rewrite <- stable_sort_app; trivial; rewrite firstn_skipn; reflexivity.
  + rewrite skipn_length; lia.
  + rewrite firstn_length; lia.
Qed.

Theorem msort_stable_sort : forall l, Forall P l -> msort le l = stable_sort le l.
Proof. intros l Hl; apply msort_fuel_stable_sort; trivial. Qed.

End Msort.

Lemma sort_on_nil :
  forall (X : Type) (keys : X -> list (value T)) (l : list X), sort_on O nil keys l = l.
Proof.
intros X keys l; unfold sort_on.
rewrite (@msort_stable_sort _ _ (fun _ => True)).
- rewrite stable_sort_trivial; [ | intros; apply refl_equal].
  rewrite map_map; simpl; apply map_id; intros; apply refl_equal.
- intros; left; reflexivity.
- intros; reflexivity.
- apply Forall_forall; intros; exact I.
Qed.

Lemma sort_on_nil_old :
  forall (X : Type) (keys : X -> list (value T)) (l : list X),
    map (@snd _ _) (stable_sort (fun x y => keys_le O nil (fst x) (fst y)) (map (fun x => (keys x, x)) l)) = l.
Proof.
intros X keys l.
rewrite stable_sort_trivial; [ | intros; apply refl_equal].
rewrite map_map; simpl; apply map_id; intros; apply refl_equal.
Qed.

(** * Failed rows *)

Lemma existsb_false_filter :
  forall (X : Type) (f : X -> bool) (l : list X), existsb f l = false -> filter f l = nil.
Proof.
intros X f l; induction l as [ | x l]; simpl; [intros; apply refl_equal | ].
case (f x); simpl; [discriminate | apply IHl].
Qed.

(** [keep_errors] adds nothing to a result which is all its input. *)
Lemma keep_errors_self : forall l, keep_errors O l l = l.
Proof.
intros l; unfold keep_errors.
case_eq (existsb (row_error O) l); intro H; [apply refl_equal | ].
rewrite existsb_false_filter; [ | assumption]; simpl; apply app_nil_r.
Qed.

(** ... nor to a result whose input holds no failed row. *)
Lemma keep_errors_no_error : 
  forall r all, existsb (row_error O) all = false -> keep_errors O r all = r.
Proof.
intros r all H; unfold keep_errors.
case (existsb (row_error O) r); [apply refl_equal | ].
rewrite existsb_false_filter; [ | assumption]; simpl; apply app_nil_r.
Qed.

Lemma eval_order_unfold :
  forall ce env q lo off lim,
    eval_squery ce env (SQ_Order q lo off lim) =
    let rows := 
        match q with
        | SQ_Select sp => eval_sspec ce env sp (map (fun o => match o with O_By e _ _ => e end) lo)
        | _ => map (fun t => (t, slice_t T relname t :: env)) (eval_squery ce env q)
        end in
    let keys (x : tuple * senv T relname) :=
        map (fun o => match o with
                      | O_By e _ _ => 
                        match is_output_col (fst x) e with
                        | Some v => v
                        | None => eval_sexpr ce (snd x) e
                        end
                      end) lo in
    let rows := map (fun x => if existsb (is_error O) (keys x) then (err_row O (fst x), snd x) else x) rows in
    keep_errors O (map (@fst _ _) (offset_limit off lim (sort_on O (map (@sorder_spec _ _) lo) keys rows)))
                (map (@fst _ _) rows).
Proof.
intros ce env q lo off lim; destruct q; apply refl_equal.
Qed.

(** A query without ORDER BY, OFFSET nor LIMIT. *)
Theorem order_by_nothing :
  forall ce env q, eval_squery ce env (SQ_Order q nil None None) = eval_squery ce env q.
Proof.
intros ce env q; rewrite eval_order_unfold; cbv zeta; unfold offset_limit.
simpl map at 2; rewrite sort_on_nil.
rewrite (map_ext (fun x : tuple * senv T relname => 
                    if existsb (is_error O) (map (fun o => match o with O_By e _ _ => match is_output_col (fst x) e with Some v => v | None => eval_sexpr ce (snd x) e end end) nil) 
                    then (err_row O (fst x), snd x) else x) (fun x => x)); [ | intros; apply refl_equal].
rewrite map_id, keep_errors_self.
- destruct q; try (rewrite map_map; simpl; apply map_id; intros; apply refl_equal).
  apply refl_equal.
- intros; apply refl_equal.
Qed.

(** * Joins *)

(** An inner join is the selection, by its condition, of a cross product. *)
Lemma inner_join_is_filter :
  forall s1 s2 (l1 l2 : list tuple) on,
    eval_join T J_Inner s1 s2 l1 (fun _ => l2) l2 on (fun t => t) = filter on (cross_product T l1 l2).
Proof.
intros s1 s2 l1 l2 on; unfold eval_join, cross_product.
induction l1 as [ | t1 l1]; [apply refl_equal | ].
simpl; rewrite filter_app, IHl1, List.map_id; apply refl_equal.
Qed.

Lemma filter_true :
  forall (X : Type) (f : X -> bool) (l : list X), (forall x, f x = true) -> filter f l = l.
Proof.
intros X f l H; induction l as [ | x l]; [apply refl_equal | ].
simpl; rewrite H, IHl; apply refl_equal.
Qed.

Lemma filter_map_ext_in :
  forall (X : Type) (f g : X -> bool) (m : X -> X) (l : list X),
    (forall x, In x l -> f x = g x /\ (f x = true -> m x = x)) -> 
    map m (filter f l) = filter g l.
Proof.
intros X f g m l; induction l as [ | x l]; intro H; [apply refl_equal | ].
simpl; destruct (H x (or_introl _ (refl_equal _))) as [H1 H2].
rewrite <- H1; case_eq (f x); intro Hx.
- simpl; rewrite H2, IHl; [apply refl_equal | | assumption].
  intros; apply H; right; assumption.
- apply IHl; intros; apply H; right; assumption.
Qed.

Lemma join_flat_map :
  forall (f : tuple -> bool) (m : tuple -> tuple) (l1 l2 : list tuple),
    flat_map (fun t1 => map m (filter f (map (join_tuple T t1) l2))) l1 = 
    map m (filter f (cross_product T l1 l2)).
Proof.
intros f m l1 l2; unfold cross_product; induction l1 as [ | t1 l1]; [apply refl_equal | ].
simpl; rewrite filter_app, map_app, IHl1; apply refl_equal.
Qed.

(** When no row fails, and the condition fails on no combination of rows, an inner join is the
    selection of the cross product by its condition. *)
Theorem inner_join_spec :
  forall ce env f1 f2 c,
    let l1 := eval_sfrom ce env f1 in
    let l2 := eval_sfrom ce env f2 in
    existsb (row_error O) (l1 ++ l2) = false ->
    (forall t, In t (cross_product T l1 l2) -> 
               row_error O t = false /\ scond_raises ce (slice_t T relname t :: env) c = false) ->
    eval_sfrom ce env (Fr_Join J_Inner false f1 f2 c) =
    filter (fun t => is_true3 T (eval_scond ce (slice_t T relname t :: env) c)) (cross_product T l1 l2).
Proof.
intros ce env f1 f2 c l1 l2 H1 H2.
change ((if existsb (row_error O) (l1 ++ l2) then keep_errors O 
          (eval_join T J_Inner (sfrom_sort ORN basesort ce f1) (sfrom_sort ORN basesort ce f2) l1 (fun _ => l2) l2
             (fun t => (existsb (row_error O) (l1 ++ l2) && row_error O t) || scond_raises ce (slice_t T relname t :: env) c || 
                       is_true3 T (eval_scond ce (slice_t T relname t :: env) c))
             (fun t => if scond_raises ce (slice_t T relname t :: env) c then err_row O t else t))
          (l1 ++ l2) else
          eval_join T J_Inner (sfrom_sort ORN basesort ce f1) (sfrom_sort ORN basesort ce f2) l1 (fun _ => l2) l2
             (fun t => (existsb (row_error O) (l1 ++ l2) && row_error O t) || scond_raises ce (slice_t T relname t :: env) c || 
                       is_true3 T (eval_scond ce (slice_t T relname t :: env) c))
             (fun t => if scond_raises ce (slice_t T relname t :: env) c then err_row O t else t)) = 
        filter (fun t => is_true3 T (eval_scond ce (slice_t T relname t :: env) c)) (cross_product T l1 l2)).
rewrite H1; simpl andb; cbv beta.
unfold eval_join; cbv beta iota zeta.
rewrite join_flat_map.
apply filter_map_ext_in.
intros t Ht; destruct (H2 t Ht) as [Ha Hb]; rewrite Hb; split; [apply refl_equal | intros; apply refl_equal].
Qed.

(** A condition on the rows of an inner join can be moved into its [ON] condition ("predicate
    pushdown", TODO 3.2), when no row fails and no condition raises an error. This does not hold for an
    outer join: a row of the left operand without a match is kept (with NULLs) by [ON], but removed by a
    [WHERE] on the right columns (see [src/testing/Test_Joins.v]). *)
Theorem inner_join_where :
  forall ce env f1 f2 c p,
    let l1 := eval_sfrom ce env f1 in
    let l2 := eval_sfrom ce env f2 in
    existsb (row_error O) (l1 ++ l2) = false ->
    (forall t, In t (cross_product T l1 l2) ->
               row_error O t = false /\ scond_raises ce (slice_t T relname t :: env) c = false /\
               scond_raises ce (slice_t T relname t :: env) (C_Conj And_F c p) = false) ->
    filter (fun t => is_true3 T (eval_scond ce (slice_t T relname t :: env) p))
           (eval_sfrom ce env (Fr_Join J_Inner false f1 f2 c)) =
    eval_sfrom ce env (Fr_Join J_Inner false f1 f2 (C_Conj And_F c p)).
Proof.
intros ce env f1 f2 c p l1 l2 H1 H2.
rewrite (inner_join_spec ce env f1 f2 c H1); 
  [ | intros t Ht; destruct (H2 t Ht) as [Ha [Hb _]]; split; assumption].
rewrite (inner_join_spec ce env f1 f2 (C_Conj And_F c p) H1); 
  [ | intros t Ht; destruct (H2 t Ht) as [Ha [_ Hc]]; split; assumption].
rewrite filter_filter.
apply filter_ext; intro t.
replace (eval_scond ce (slice_t T relname t :: env) (C_Conj And_F c p))
  with (Bool.andb (B T) (eval_scond ce (slice_t T relname t :: env) c) (eval_scond ce (slice_t T relname t :: env) p))
  by reflexivity.
unfold is_true3; rewrite Bool.is_true_andb.
destruct (Bool.is_true (B T) (eval_scond ce (slice_t T relname t :: env) p));
  destruct (Bool.is_true (B T) (eval_scond ce (slice_t T relname t :: env) c)); apply refl_equal.
Qed.

(** The rows of a left join which are not padded with NULLs are those of the
    inner join: a left join without unmatched row is an inner join. *)
Lemma left_join_no_padding :
  forall s1 s2 (l1 l2 : list tuple) on mark,
    (forall t1, In t1 l1 -> filter on (map (join_tuple T t1) l2) <> nil) ->
    eval_join T J_Left s1 s2 l1 (fun _ => l2) l2 on mark =
    eval_join T J_Inner s1 s2 l1 (fun _ => l2) l2 on mark.
Proof.
intros s1 s2 l1 l2 on mark; unfold eval_join.
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
    is_hidden env (E_Case c e1 e2) = false ->
    scond_raises ce env c = false ->
    is_true3 T (eval_scond ce env c) = true ->
    eval_sexpr ce env (E_Case c e1 e2) = eval_sexpr ce env e1.
Proof.
intros ce env c e1 e2 Hh Hr H.
change ((if is_hidden env (E_Case c e1 e2) then null O 
         else if scond_raises ce env c then error O "error"%string
         else if is_true3 T (eval_scond ce env c) then eval_sexpr ce env e1 else eval_sexpr ce env e2) =
        eval_sexpr ce env e1).
rewrite Hh, Hr, H; apply refl_equal.
Qed.

Lemma eval_case_not_true :
  forall ce env c e1 e2,
    is_hidden env (E_Case c e1 e2) = false ->
    scond_raises ce env c = false ->
    is_true3 T (eval_scond ce env c) = false ->
    eval_sexpr ce env (E_Case c e1 e2) = eval_sexpr ce env e2.
Proof.
intros ce env c e1 e2 Hh Hr H.
change ((if is_hidden env (E_Case c e1 e2) then null O 
         else if scond_raises ce env c then error O "error"%string
         else if is_true3 T (eval_scond ce env c) then eval_sexpr ce env e1 else eval_sexpr ce env e2) =
        eval_sexpr ce env e2).
rewrite Hh, Hr, H; apply refl_equal.
Qed.

(** A failed argument makes a function fail, unless the function is lazy and the argument is not
    its first one. *)
Lemma eval_fun_error :
  forall ce env f e l,
    is_hidden env (E_Fun f (e :: l)) = false ->
    is_error O (eval_sexpr ce env e) = true ->
    eval_sexpr ce env (E_Fun f (e :: l)) = eval_sexpr ce env e.
Proof.
intros ce env f e l Hh He.
change ((if is_hidden env (E_Fun f (e :: l)) then null O 
         else match first_error O (if lazy_symbol O f then firstn 1 (map (eval_sexpr ce env) (e :: l)) 
                                   else map (eval_sexpr ce env) (e :: l)) with
              | Some err => err
              | None => interp_symbol T f (map (eval_sexpr ce env) (e :: l))
              end) = eval_sexpr ce env e).
rewrite Hh; unfold first_error; case (lazy_symbol O f); simpl; rewrite He; apply refl_equal.
Qed.

(** An aggregate of the current block, without DISTINCT nor FILTER, is the
    aggregate of the values of its argument on the tuples of the group. *)
Lemma existsb_const_false : forall (X : Type) (l : list X), existsb (fun _ => false) l = false.
Proof. intros X l; induction l; [apply refl_equal | assumption]. Qed.

Lemma eval_agg_group :
  forall ce env sa g ag a,
    a inS sa ->
    existsb (row_error O) g = false ->
    (forall t, In t g -> is_error O (dot T t a) = false) ->
    eval_sexpr ce ((sa, g, nil) :: env) (E_Agg ag Set_All (E_Col T relname a) (C_True T relname)) =
    interp_aggregate T ag (map (fun t => dot T t a) g).
Proof.
intros ce env sa g ag a Ha Hg Hv.
change (match agg_env (a :: nil) ((sa, g, nil) :: env) with
        | nil => interp_aggregate T ag nil
        | (sa', g', _) :: env' =>
          if existsb (row_error O) g' || existsb (fun t => false) g'
          then error O "error"%string
          else 
            let vals := map (fun t => lookup ((sa', t :: nil, nil) :: env') a)
                            (filter (fun t => is_true3 T (Bool.true (B T))) g') in
            match first_error O vals with
            | Some err => err
            | None => interp_aggregate T ag vals
            end
        end = interp_aggregate T ag (map (fun t => dot T t a) g)).
unfold agg_env; simpl; rewrite Ha; simpl.
rewrite Hg, existsb_const_false; simpl.
rewrite filter_true; [ | intro t; unfold is_true3; rewrite Bool.true_is_true; apply refl_equal].
rewrite (map_ext_in _ (fun t => dot T t a)); [ | intros t Ht; simpl; rewrite Ha; apply refl_equal].
case_eq (first_error O (map (fun t => dot T t a) g)); [ | intros; apply refl_equal].
intros v Hf; unfold first_error in Hf; apply find_some in Hf; destruct Hf as [Hf1 Hf2].
rewrite in_map_iff in Hf1; destruct Hf1 as [t [Ht1 Ht2]]; subst v.
rewrite (Hv t Ht2) in Hf2; discriminate.
Qed.

(** * Set operations *)

(** [UNION ALL] is the concatenation, when the dialect does not convert the values of the columns of a
    set operation (PostgreSQL, SQLite; MySQL converts decimals to a common scale) and the rows are
    tuples ([mk_tuple] of the labels and [dot] of a tuple is that tuple) *)
Lemma union_all_spec :
  forall ce env q1 q2,
    (forall l, unify_column O l = l) ->
    (forall atts rows, unify_rows O atts rows = rows) ->
    Fset.equal (A T) (squery_sort ORN basesort ce q1) (squery_sort ORN basesort ce q2) = true ->
    eval_squery ce env (SQ_Set Union Set_All q1 q2) = 
    eval_squery ce env q1 ++ eval_squery ce env q2.
Proof.
intros ce env q1 q2 _ Hu H.
change ((if Fset.equal (A T) (squery_sort ORN basesort ce q1) (squery_sort ORN basesort ce q2)
         then unify_rows O ({{{squery_sort ORN basesort ce q1}}})
                (keep_errors O (eval_set_op O Union Set_All (eval_squery ce env q1) (eval_squery ce env q2))
                          (eval_squery ce env q1 ++ eval_squery ce env q2))
         else nil) = eval_squery ce env q1 ++ eval_squery ce env q2).
rewrite H, Hu; apply keep_errors_self.
Qed.

(** [DISTINCT] is idempotent (TODO 6.4): removing the duplicates of a list without duplicates changes
    nothing, whatever the projection [f] on which the rows are compared *)
Lemma dedup_rec_idem :
  forall (X : Type) (f : X -> tuple) seen l,
    dedup_rec O f seen (dedup_rec O f seen l) = dedup_rec O f seen l.
Proof.
intros X f seen l; revert seen; induction l as [ | x l IH]; intro seen; simpl; [reflexivity | ].
case_eq (tuple_mem O (f x) seen); intro H.
- apply IH.
- simpl; rewrite H, IH; reflexivity.
Qed.

(** the balanced tree of [dedup_tree] holds the canonical forms of the tuples of the list of [dedup_rec] *)
Lemma dedup_tree_rec :
  forall (X : Type) (f : X -> tuple) l st sl,
    FiniteSetImpl.Ok (OTuple T) st ->
    (forall c, FiniteSetImpl.InT (OTuple T) c st <->
               Oeset.mem_bool (OTuple T) c (map (canon_tuple O) sl) = true) ->
    dedup_tree O f st l = dedup_rec O f sl l.
Proof.
intros X f l; induction l as [ | x l IH]; intros st sl Ok H; [reflexivity | ].
simpl; unfold tuple_mem.
case_eq (Oeset.mem_bool (OTuple T) (canon_tuple O (f x)) (map (canon_tuple O) sl)); intro K.
- rewrite (proj2 (@FiniteSetImpl.mem_spec _ (OTuple T) st _ Ok) (proj2 (H _) K)); apply IH; trivial.
- case_eq (FiniteSetImpl.mem (OTuple T) (canon_tuple O (f x)) st); intro M.
  + rewrite (proj1 (H _) (proj1 (@FiniteSetImpl.mem_spec _ (OTuple T) st _ Ok) M)) in K; discriminate K.
  + apply f_equal; apply IH; [apply (@FiniteSetImpl.add_ok _ (OTuple T)); exact Ok | ].
    intro c; simpl map; rewrite (Oeset.mem_bool_unfold _ c (_ :: _)).
    generalize (@FiniteSetImpl.add_spec _ (OTuple T) st (canon_tuple O (f x)) c Ok) (H c).
    destruct (Oeset.compare (OTuple T) c (canon_tuple O (f x))); simpl; intuition; try discriminate.
Qed.

Lemma dedup_on_rec :
  forall (X : Type) (f : X -> tuple) l, dedup_on O f l = dedup_rec O f nil l.
Proof.
intros X f l; apply dedup_tree_rec; [apply (@FiniteSetImpl.empty_ok _ (OTuple T)) | ].
intro c; split; intro K; [inversion K | discriminate K].
Qed.

Theorem dedup_idem : forall l, dedup O (dedup O l) = dedup O l.
Proof. intro l; unfold dedup; rewrite !dedup_on_rec; apply dedup_rec_idem. Qed.

(** The grouping sets of [ROLLUP (e1, ..., en)]: [n + 1] sets, from all the expressions to none; those of
    [CUBE (e1, ..., en)]: [2 ^ n] sets, all the sublists (TODO 6.4) *)
Lemma rollup_sets_length : forall (A : Type) (l : list A), List.length (rollup_sets l) = S (List.length l).
Proof. intros A l; unfold rollup_sets; rewrite map_length, rev_length, seq_length; reflexivity. Qed.


Lemma cube_sets_length : forall (A : Type) (l : list A), List.length (cube_sets l) = Nat.pow 2 (List.length l).
Proof.
intros A l; induction l as [ | x l IH]; simpl; [reflexivity | ].
rewrite app_length, map_length, IH; lia.
Qed.

(** Window frames (TODO 6.4): [ROWS BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW] is the running frame, the rows
    from the first one to the current one; [ROWS BETWEEN UNBOUNDED PRECEDING AND UNBOUNDED FOLLOWING] is the whole
    partition *)
Lemma filter_le_seq : forall i n, filter (fun j => PeanoNat.Nat.leb j i) (seq 0 n) = seq 0 (PeanoNat.Nat.min n (S i)).
Proof.
intros i n; induction n as [ | n IH]; [reflexivity | ].
rewrite seq_S, filter_app, IH, PeanoNat.Nat.add_0_l; cbn [filter].
case_eq (PeanoNat.Nat.leb n i); intro H.
- apply PeanoNat.Nat.leb_le in H.
  replace (PeanoNat.Nat.min n (S i)) with n by lia; replace (PeanoNat.Nat.min (S n) (S i)) with (S n) by lia.
  rewrite seq_S; reflexivity.
- apply PeanoNat.Nat.leb_gt in H.
  replace (PeanoNat.Nat.min n (S i)) with (S i) by lia; replace (PeanoNat.Nat.min (S n) (S i)) with (S i) by lia.
  apply app_nil_r.
Qed.

Theorem frame_running :
  forall n gidx rk i, (S i <= n)%nat ->
    frame_positions (Frame_Rows Unbounded_Preceding Current_Row) n gidx rk i = seq 0 (S i).
Proof.
intros n gidx rk i H; simpl.
rewrite filter_le_seq, PeanoNat.Nat.min_r; [reflexivity | exact H].
Qed.

Theorem frame_whole_partition :
  forall n gidx rk i, frame_positions (Frame_Rows Unbounded_Preceding Unbounded_Following) n gidx rk i = seq 0 n.
Proof.
intros n gidx rk i; simpl.
induction (seq 0 n) as [ | x l IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

(** the positions of [seq 0 n] in an interval [a .. b] *)
Lemma filter_interval :
  forall a b n,
    filter (fun j => PeanoNat.Nat.leb a j && PeanoNat.Nat.leb j b) (seq 0 n) =
    seq a (PeanoNat.Nat.min (S b) n - a).
Proof.
intros a b n; induction n as [ | n IH]; [rewrite PeanoNat.Nat.min_0_r; reflexivity | ].
rewrite seq_S, filter_app, IH, PeanoNat.Nat.add_0_l; cbn [filter].
case_eq (PeanoNat.Nat.leb a n); intro Ha; [apply PeanoNat.Nat.leb_le in Ha | apply PeanoNat.Nat.leb_gt in Ha];
  case_eq (PeanoNat.Nat.leb n b); intro Hb; try apply PeanoNat.Nat.leb_le in Hb;
  try apply PeanoNat.Nat.leb_gt in Hb; cbn [andb].
- replace (PeanoNat.Nat.min (S b) (S n) - a) with (S (PeanoNat.Nat.min (S b) n - a)) by lia.
  rewrite seq_S; do 2 f_equal; lia.
- rewrite app_nil_r; f_equal; lia.
- rewrite app_nil_r; f_equal; lia.
- rewrite app_nil_r; f_equal; lia.
Qed.

Lemma filter_from :
  forall a n, filter (fun j => PeanoNat.Nat.leb a j) (seq 0 n) = seq a (n - a).
Proof.
intros a n; induction n as [ | n IH]; [reflexivity | ].
rewrite seq_S, filter_app, IH, PeanoNat.Nat.add_0_l; cbn [filter].
case_eq (PeanoNat.Nat.leb a n); intro Ha; [apply PeanoNat.Nat.leb_le in Ha | apply PeanoNat.Nat.leb_gt in Ha].
- replace (S n - a) with (S (n - a)) by lia; rewrite seq_S; do 2 f_equal; lia.
- rewrite app_nil_r; f_equal; lia.
Qed.

(** [ROWS BETWEEN k PRECEDING AND m FOLLOWING] is the interval of the rows [i - k .. i + m] of the partition *)
Theorem frame_rows_bounded :
  forall n gidx rk i k m,
    frame_positions (Frame_Rows (Preceding k) (Following m)) n gidx rk i =
    seq (i - k) (PeanoNat.Nat.min (S (i + m)) n - (i - k)).
Proof.
intros n gidx rk i k m; cbn [frame_positions after_start before_end]; rewrite <- filter_interval.
apply filter_ext; intro j.
case_eq (PeanoNat.Nat.leb i (j + k)); intro H1; [apply PeanoNat.Nat.leb_le in H1 | apply PeanoNat.Nat.leb_gt in H1];
  case_eq (PeanoNat.Nat.leb (i - k) j); intro H2; try apply PeanoNat.Nat.leb_le in H2;
  try apply PeanoNat.Nat.leb_gt in H2; try reflexivity; lia.
Qed.

(** [ROWS BETWEEN CURRENT ROW AND CURRENT ROW] is the current row *)
Theorem frame_current_row :
  forall n gidx rk i, (i < n)%nat -> frame_positions (Frame_Rows Current_Row Current_Row) n gidx rk i = i :: nil.
Proof.
intros n gidx rk i H; cbn [frame_positions after_start before_end]; rewrite filter_interval.
replace (PeanoNat.Nat.min (S i) n - i) with 1 by lia; reflexivity.
Qed.

(** [ROWS BETWEEN CURRENT ROW AND UNBOUNDED FOLLOWING] is the rest of the partition *)
Theorem frame_to_end :
  forall n gidx rk i,
    frame_positions (Frame_Rows Current_Row Unbounded_Following) n gidx rk i = seq i (n - i).
Proof.
intros n gidx rk i; cbn [frame_positions after_start before_end]; rewrite <- filter_from.
apply filter_ext; intro j; apply andb_true_r.
Qed.

(** [EXCLUDE NO OTHERS] excludes nothing *)
Theorem frame_exclude_no_others :
  forall fr n gidx rk i, frame_positions (Frame_Excl fr Excl_No_Others) n gidx rk i = frame_positions fr n gidx rk i.
Proof.
intros fr n gidx rk i; simpl.
induction (frame_positions fr n gidx rk i) as [ | x l IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma filter_true_seq : forall (f : nat -> bool) n, (forall j, f j = true) -> filter f (seq 0 n) = seq 0 n.
Proof.
intros f n H; induction (seq 0 n) as [ | x l IH]; simpl; [reflexivity | rewrite H, IH; reflexivity].
Qed.

(** [RANGE] and [GROUPS] [BETWEEN UNBOUNDED PRECEDING AND UNBOUNDED FOLLOWING] are the whole partition *)
Theorem frame_range_whole :
  forall n gidx rk i, frame_positions (Frame_Range Unbounded_Preceding Unbounded_Following) n gidx rk i = seq 0 n.
Proof. intros n gidx rk i; apply filter_true_seq; reflexivity. Qed.

Theorem frame_groups_whole :
  forall n gidx rk i, frame_positions (Frame_Groups Unbounded_Preceding Unbounded_Following) n gidx rk i = seq 0 n.
Proof. intros n gidx rk i; apply filter_true_seq; reflexivity. Qed.

(** [RANGE BETWEEN CURRENT ROW AND CURRENT ROW] is the peers of the current row (the rows of the same group of
    the [ORDER BY] keys), and so is [GROUPS BETWEEN CURRENT ROW AND CURRENT ROW] *)
Theorem frame_range_current_peers :
  forall n gidx rk i,
    frame_positions (Frame_Range Current_Row Current_Row) n gidx rk i =
    filter (fun j => PeanoNat.Nat.eqb (nth j gidx 0) (nth i gidx 0)) (seq 0 n).
Proof.
intros n gidx rk i; cbn [frame_positions range_after_start range_before_end]; apply filter_ext; intro j.
destruct (PeanoNat.Nat.leb_spec (nth i gidx 0) (nth j gidx 0));
  destruct (PeanoNat.Nat.leb_spec (nth j gidx 0) (nth i gidx 0));
  destruct (PeanoNat.Nat.eqb_spec (nth j gidx 0) (nth i gidx 0)); simpl; trivial; lia.
Qed.

Theorem frame_groups_current_peers :
  forall n gidx rk i,
    frame_positions (Frame_Groups Current_Row Current_Row) n gidx rk i =
    filter (fun j => PeanoNat.Nat.eqb (nth j gidx 0) (nth i gidx 0)) (seq 0 n).
Proof.
intros n gidx rk i; cbn [frame_positions after_start before_end]; apply filter_ext; intro j.
destruct (PeanoNat.Nat.leb_spec (nth i gidx 0) (nth j gidx 0));
  destruct (PeanoNat.Nat.leb_spec (nth j gidx 0) (nth i gidx 0));
  destruct (PeanoNat.Nat.eqb_spec (nth j gidx 0) (nth i gidx 0)); simpl; trivial; lia.
Qed.

(** the default frame with an [ORDER BY], [RANGE BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW], is the rows up to
    the last peer of the current row *)
Theorem frame_range_running :
  forall n gidx rk i,
    frame_positions (Frame_Range Unbounded_Preceding Current_Row) n gidx rk i =
    filter (fun j => PeanoNat.Nat.leb (nth j gidx 0) (nth i gidx 0)) (seq 0 n).
Proof. intros n gidx rk i; reflexivity. Qed.

(** The bound of the recursion does not matter once a fixpoint is reached (TODO 6.4): if the iteration of
    [WITH RECURSIVE] reaches an empty working table within [n] steps, any larger bound gives the same rows *)
Fixpoint done_within (step : list tuple -> list tuple) (d : bool) (n : nat) (acc work : list tuple) : bool :=
  match n with
  | 0 => match work with nil => true | _ => false end
  | S n' =>
    match work with
    | nil => true
    | _ => let new := step work in
           let new' := if d then eval_set_op O Diff Set_Distinct new acc else new in
           done_within step d n' (acc ++ new') new'
    end
  end.

Theorem rec_loop_fuel :
  forall step d sa n m acc work,
    done_within step d n acc work = true ->
    rec_loop O step d sa (n + m) acc work = rec_loop O step d sa n acc work.
Proof.
intros step d sa n; induction n as [ | n IH]; intros m acc work H; simpl in H.
- destruct work; [ | discriminate H]; simpl; destruct m; reflexivity.
- destruct work as [ | x work]; [reflexivity | ].
  simpl; apply IH; exact H.
Qed.

(** [UNION ALL] is commutative as a bag (TODO 6.4): the rows are the same, in another order *)
Theorem union_all_comm :
  forall ce env q1 q2,
    (forall l, unify_column O l = l) ->
    (forall atts rows, unify_rows O atts rows = rows) ->
    Fset.equal (A T) (squery_sort ORN basesort ce q1) (squery_sort ORN basesort ce q2) = true ->
    Fset.equal (A T) (squery_sort ORN basesort ce q2) (squery_sort ORN basesort ce q1) = true ->
    Permutation (eval_squery ce env (SQ_Set Union Set_All q1 q2))
                (eval_squery ce env (SQ_Set Union Set_All q2 q1)).
Proof.
intros ce env q1 q2 Hc Hu H12 H21.
rewrite (union_all_spec ce env q1 q2 Hc Hu H12), (union_all_spec ce env q2 q1 Hc Hu H21).
apply Permutation_app_comm.
Qed.

(** [UNION ALL] is associative (as lists: the same rows in the same order) *)
Theorem union_all_assoc :
  forall ce env q1 q2 q3,
    (forall l, unify_column O l = l) ->
    (forall atts rows, unify_rows O atts rows = rows) ->
    Fset.equal (A T) (squery_sort ORN basesort ce q1) (squery_sort ORN basesort ce q2) = true ->
    Fset.equal (A T) (squery_sort ORN basesort ce q2) (squery_sort ORN basesort ce q3) = true ->
    Fset.equal (A T) (squery_sort ORN basesort ce q1) (squery_sort ORN basesort ce q3) = true ->
    eval_squery ce env (SQ_Set Union Set_All q1 (SQ_Set Union Set_All q2 q3)) =
    eval_squery ce env (SQ_Set Union Set_All (SQ_Set Union Set_All q1 q2) q3).
Proof.
intros ce env q1 q2 q3 Hc Hu H12 H23 H13.
assert (E1 : squery_sort ORN basesort ce (SQ_Set Union Set_All q2 q3) = squery_sort ORN basesort ce q2);
  [reflexivity | ].
assert (E2 : squery_sort ORN basesort ce (SQ_Set Union Set_All q1 q2) = squery_sort ORN basesort ce q1);
  [reflexivity | ].
rewrite (union_all_spec ce env q1 (SQ_Set Union Set_All q2 q3) Hc Hu); [ | rewrite E1; exact H12].
rewrite (union_all_spec ce env (SQ_Set Union Set_All q1 q2) q3 Hc Hu); [ | rewrite E2; exact H13].
rewrite (union_all_spec ce env q2 q3 Hc Hu H23), (union_all_spec ce env q1 q2 Hc Hu H12).
apply app_assoc.
Qed.

End Sec.
