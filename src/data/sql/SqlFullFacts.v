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

Lemma sort_on_nil :
  forall (X : Type) (keys : X -> list (value T)) (l : list X), sort_on O nil keys l = l.
Proof.
intros X keys l; unfold sort_on.
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
