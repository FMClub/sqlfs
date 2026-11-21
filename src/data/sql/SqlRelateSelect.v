(** * The selections of [Sql.v] and of [SqlFull.v] agree (TODO 6.1)

    The blocks [SELECT s FROM q WHERE f] of [Sql.v] without grouping, whose [SELECT] list and [WHERE] formula are
    built from function terms and predicates, translate to [SqlFull.v] ([ft_to], [f_to], [s_to]); the two
    semantics give the same bag of rows when the [FROM] query does ([select_agree]). The dialect of [SqlFull.v] is
    the one of the instance: its functions, predicates and literals are those of [T] ([Hfun], [Hpred],
    [Hconst]), it converts nothing before a comparison ([Hcoerce]), no value is a failure ([Herr], [Hpe]: [Sql.v]
    has no errors), and a NULL has no type ([Hnull]: [SqlFull.v] stores a NULL with the type of its column,
    [Sql.v] keeps the value).

    Grouped blocks [SELECT s FROM q1, ..., qn WHERE f GROUP BY t1, ..., tk] (k > 0, [HAVING] true) whose items
    are, outside the aggregates, built on the grouping terms and, inside, on the columns of the [FROM] clause
    ([gcheck]) translate too ([at_to2], [item_to]); [select_agree_grp]: the two semantics give the same bag, for a
    dialect whose aggregates are those of the instance ([Hagg]) and do not depend on the order of their input
    ([Hperm]), and whose canonical form of a value identifies only equal values ([Hcv]). The groups of [Sql.v]
    ([partition]) are those of [SqlFull.v] ([group_on_list]), in the same order, each reversed
    ([partition_groups]); a term built on the grouping terms has one value on a group ([built_const]), and an
    aggregate is computed over the rows of the group on both sides ([agg_sql], [agg_full]). *)
Require Import List Bool NArith Permutation.
Require Import BasicFacts ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection ListPermut ListSort Join Projection
        FlatData Bool3 Formula Sql SqlFull SqlRelate SqlGroupFacts Partition.

Section Sec.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.
Hypothesis ORN : Oset.Rcd relname.
Hypothesis O : dialect T.
Hypothesis basesort : relname -> Fset.set (Tuple.A T).
Hypothesis instance : relname -> Febag.bag (Fecol.CBag (Tuple.CTuple T)).

Import Tuple.

Notation BTupleT := (Fecol.CBag (CTuple T)).
Notation sexpr := (SqlFull.sexpr T relname).
Notation scond := (SqlFull.scond T relname).

Hypothesis Herr : forall v, is_error O v = false.
Hypothesis Hpe : forall p l, pred_error O p l = false.
Hypothesis Hcoerce : forall p ks l, cmp_coerce O p ks l = l.
Hypothesis Hpred : forall p l, interp_pred O p l = interp_predicate T p l.
Hypothesis Hfun : forall f l, interp_fun O f l = interp_symbol T f l.
Hypothesis Hconst : forall v, const_of O v = v.
Hypothesis Hnull : forall a v, is_null O v = true -> null_of T a = v.

(** * Translation *)

Fixpoint ft_to (t : funterm T) : sexpr :=
  match t with
  | F_Constant _ c => E_Const T relname c
  | F_Dot _ a => E_Col T relname a
  | F_Expr _ f l => E_Fun f (map ft_to l)
  end.

Definition at_to (t : aggterm T) : option sexpr :=
  match t with A_Expr _ ft => Some (ft_to ft) | _ => None end.

Fixpoint lopt {X Y : Type} (f : X -> option Y) (l : list X) : option (list Y) :=
  match l with
  | nil => Some nil
  | x :: l => match f x, lopt f l with Some y, Some l' => Some (y :: l') | _, _ => None end
  end.

Fixpoint f_to (f : sql_formula T (sql_query T relname)) : option scond :=
  match f with
  | Sql_Conj a f1 f2 => match f_to f1, f_to f2 with Some c1, Some c2 => Some (C_Conj a c1 c2) | _, _ => None end
  | Sql_Not f => option_map (@C_Not T relname) (f_to f)
  | Sql_True _ _ => Some (C_True T relname)
  | Sql_Pred _ p l => option_map (@C_Pred T relname p) (lopt at_to l)
  | _ => None
  end.

Definition s_to (s : select_item T) : option (sselect T relname) :=
  match s with
  | Select_Star _ => Some (S_Star T relname)
  | Select_List _ (_Select_List _ l) =>
    option_map (@S_List T relname)
      (lopt (fun x => match x with Select_As _ e a => option_map (fun e' => S_As e' a) (at_to e) end) l)
  end.

(** * Agreement of the terms and formulas *)

Notation ev := (eval_sexpr ORN O basesort instance).
Notation ec := (eval_scond ORN O basesort instance).
Notation er := (scond_raises ORN O basesort instance).

Lemma first_error_none : forall l, first_error O l = None.
Proof. intro l; induction l as [ | v l IH]; [reflexivity | unfold first_error; simpl; rewrite Herr; exact IH]. Qed.

Lemma quicksort_one : forall t, quicksort (OTuple T) (t :: nil) = t :: nil.
Proof. intro t; apply quicksort_1. Qed.

Lemma ft_agree : forall ce t ft, ev ce (slice_t T relname t :: nil) (ft_to ft) = interp_funterm T (env_t T nil t) ft.
Proof.
intros ce t; fix IH 1; intros [c | a | f l].
- cbn; apply Hconst.
- cbn [eval_sexpr ft_to interp_funterm]; unfold is_hidden; cbn [lookup interp_dot env_t slice_t].
  rewrite quicksort_one; destruct (a inS? labels T t); reflexivity.
- cbn [ft_to interp_funterm]; change (ev ce (slice_t T relname t :: nil) (E_Fun f (map ft_to l))) with
    (if is_hidden (slice_t T relname t :: nil) (E_Fun f (map ft_to l)) then null O
     else let vs := map (ev ce (slice_t T relname t :: nil)) (map ft_to l) in
          match first_error O (if lazy_symbol O f then firstn 1 vs else vs) with
          | Some err => err | None => interp_fun O f vs end).
  replace (is_hidden (slice_t T relname t :: nil) (E_Fun f (map ft_to l))) with false by reflexivity.
  cbv zeta; rewrite first_error_none, Hfun, map_map; f_equal.
  induction l as [ | x l IHl]; [reflexivity | simpl; rewrite IH, IHl; reflexivity].
Qed.

Lemma lopt_at_to : forall ce t l l', lopt at_to l = Some l' ->
  map (ev ce (slice_t T relname t :: nil)) l' = map (interp_aggterm T (env_t T nil t)) l.
Proof.
intros ce t l; induction l as [ | x l IH]; intros l' H; simpl in H; [injection H; intros <-; reflexivity | ].
destruct x as [ft | ag ft | f la]; simpl in H; try discriminate H.
destruct (lopt at_to l) as [l2 | ]; [ | discriminate H]; injection H; intros <-; simpl.
rewrite ft_agree, (IH l2 eq_refl); reflexivity.
Qed.

Lemma f_agree : forall unknown contains_nulls (I : env T -> sql_query T relname -> Febag.bag BTupleT) ce t f c,
  f_to f = Some c ->
  ec ce (slice_t T relname t :: nil) c = eval_sql_formula unknown contains_nulls I (env_t T nil t) f /\
  er ce (slice_t T relname t :: nil) c = false.
Proof.
intros unknown contains_nulls I ce t f; induction f as [a f1 IH1 f2 IH2 | f IH | | p l | qtf p l q | l q | q];
  intros c H; simpl in H; try discriminate H.
- destruct (f_to f1) as [c1 | ]; [ | discriminate H]; destruct (f_to f2) as [c2 | ]; [ | discriminate H].
  injection H; intros <-; destruct (IH1 c1 eq_refl) as [E1 R1]; destruct (IH2 c2 eq_refl) as [E2 R2].
  split; cbn [eval_scond scond_raises eval_sql_formula]; fold ec er; [rewrite E1, E2; reflexivity | rewrite R1, R2; reflexivity].
- destruct (f_to f) as [c1 | ]; [ | discriminate H]; injection H; intros <-; destruct (IH c1 eq_refl) as [E R].
  split; cbn [eval_scond scond_raises eval_sql_formula]; fold ec er; [rewrite E; reflexivity | exact R].
- injection H; intros <-; split; reflexivity.
- destruct (lopt at_to l) as [l' | ] eqn:E; [ | discriminate H]; injection H; intros <-.
  cbn [eval_scond scond_raises eval_sql_formula]; fold ev; rewrite Hcoerce, Hpred, (lopt_at_to ce t l l' E), Hpe; split; [reflexivity | ].
  rewrite orb_false_r; induction (map (interp_aggterm T (env_t T nil t)) l) as [ | v vs IHv]; [reflexivity | simpl; rewrite Herr; exact IHv].
Qed.

(** * The evaluation of [Sql.v] respects the equality of tuples *)

Lemma ft_compat : forall x y, x =t= y -> forall ft, interp_funterm T (env_t T nil x) ft = interp_funterm T (env_t T nil y) ft.
Proof.
intros x y Hxy; fix IH 1; intros [c | a | f l]; [reflexivity | | ].
- cbn [interp_funterm interp_dot env_t]; rewrite !quicksort_1; exact (tuple_eq_dot T x y Hxy a).
- cbn [interp_funterm]; f_equal; induction l as [ | z l IHl]; [reflexivity | simpl; rewrite IH, IHl; reflexivity].
Qed.

Lemma f_compat : forall unknown contains_nulls (I : env T -> sql_query T relname -> Febag.bag BTupleT) f c x y,
  f_to f = Some c -> x =t= y ->
  eval_sql_formula unknown contains_nulls I (env_t T nil x) f = eval_sql_formula unknown contains_nulls I (env_t T nil y) f.
Proof.
intros unknown contains_nulls I f; induction f as [a f1 IH1 f2 IH2 | f IH | | p l | qtf p l q | l q | q];
  intros c x y H Hxy; simpl in H; try discriminate H; cbn [eval_sql_formula].
- destruct (f_to f1) as [c1 | ]; [ | discriminate H]; destruct (f_to f2) as [c2 | ]; [ | discriminate H].
  rewrite (IH1 c1 x y eq_refl Hxy), (IH2 c2 x y eq_refl Hxy); reflexivity.
- destruct (f_to f) as [c1 | ]; [ | discriminate H]; rewrite (IH c1 x y eq_refl Hxy); reflexivity.
- reflexivity.
- destruct (lopt at_to l) as [l' | ] eqn:E; [ | discriminate H]; clear H; f_equal.
  revert l' E; induction l as [ | z l IHl]; intros l' E; [reflexivity | ]; simpl in E.
  destruct z as [ft | ag ft | g la]; simpl in E; try discriminate E.
  destruct (lopt at_to l) as [l2 | ]; [ | discriminate E].
  simpl; rewrite (ft_compat x y Hxy ft), (IHl l2 eq_refl); reflexivity.
Qed.

(** * The rows of the [SELECT] list *)

Definition row_of ce (s' : sselect T relname) (t : tuple T) :=
  match s' with
  | S_Star _ _ => t
  | S_List l => mk_row O (map (fun it => match it with S_As e a => (a, ev ce (slice_t T relname t :: nil) e) end) l)
  end.

Lemma find_lopt : forall ce t (l : list (select T)) l' a, lopt (fun x => match x with Select_As _ e a => option_map (fun e' => S_As e' a) (at_to e) end) l = Some l' ->
  Oset.find (OAtt T) a (map (fun it => match it with S_As e a => (a, ev ce (slice_t T relname t :: nil) e) end) l') =
  option_map (interp_aggterm T (env_t T nil t)) (Oset.find (OAtt T) a (pairs_of_selects T (_Select_List T l))) /\
  map (@fst _ _) (map (fun it => match it with S_As e a => (a, ev ce (slice_t T relname t :: nil) e) end) l') =
  sort_of_select_list T (_Select_List T l).
Proof.
intros ce t l; induction l as [ | [e b] l IH]; intros l' a H; simpl in H; [injection H; intros <-; split; reflexivity | ].
destruct e as [ft | ag ft | g la]; simpl in H; try discriminate H.
destruct (lopt _ l) as [l2 | ] eqn:E; [ | discriminate H]; injection H; intros <-.
destruct (IH l2 a eq_refl) as [K1 K2]; simpl; split; [ | f_equal; exact K2].
unfold pairs_of_selects in K1; simpl in K1 |- *.
destruct (Oset.eq_bool (OAtt T) a b); [simpl; rewrite ft_agree; reflexivity | exact K1].
Qed.

Lemma row_agree : forall ce s s' t, s_to s = Some s' -> row_of ce s' t =t= projection T (env_t T nil t) s.
Proof.
intros ce s s' t H; destruct s as [ | [l]]; simpl in H.
- injection H; intros <-; cbn [row_of projection env_t]; rewrite quicksort_1; apply Oeset.compare_eq_refl.
- destruct (lopt _ l) as [l' | ] eqn:E; [ | discriminate H]; injection H; intros <-; cbn [row_of projection].
  unfold mk_row; rewrite tuple_eq; split.
  + rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)), (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)).
    rewrite (proj2 (find_lopt ce t l l' (err_attr O) E)); apply Fset.equal_refl.
  + intros a Ha; rewrite !dot_mk_tuple.
    rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
    rewrite (proj2 (find_lopt ce t l l' a E)) in Ha |- *; rewrite Ha.
    rewrite (proj1 (find_lopt ce t l l' a E)).
    destruct (Oset.find (OAtt T) a (pairs_of_selects T (_Select_List T l))) as [e | ]; simpl; [ | unfold default_tuple; rewrite dot_mk_tuple, Fset.empty_spec; reflexivity].
    unfold store; destruct (is_null O _) eqn:N; [apply Hnull; exact N | reflexivity].
Qed.

(** * The rows of the block in [SqlFull.v] *)

Lemma row_error_false : forall t, row_error O t = false.
Proof. intro t; unfold row_error; induction ({{{labels T t}}}) as [ | a l IH]; [reflexivity | simpl; rewrite Herr; exact IH]. Qed.

Lemma keep_errors_id : forall r all, keep_errors O r all = r.
Proof.
intros r all; unfold keep_errors.
replace (existsb (row_error O) r) with false by (induction r as [ | x r IH]; [reflexivity | simpl; rewrite row_error_false; exact IH]).
replace (filter (row_error O) all) with (@nil (tuple T)) by (induction all as [ | x all IH]; [reflexivity | simpl; rewrite row_error_false; exact IH]).
apply app_nil_r.
Qed.

Lemma has_agg_ft : forall ce sa ft, sexpr_has_agg ORN basesort ce sa (ft_to ft) = false.
Proof.
intros ce sa; fix IH 1; intros [c | a | f l]; [reflexivity | reflexivity | ].
cbn [ft_to sexpr_has_agg]; induction l as [ | x l IHl]; [reflexivity | simpl; rewrite IH; exact IHl].
Qed.

Lemma s_no_agg : forall ce sa s s', s_to s = Some s' -> sselect_has_agg ORN basesort ce sa s' = false.
Proof.
intros ce sa s s' H; destruct s as [ | [l]]; simpl in H; [injection H; intros <-; reflexivity | ].
destruct (lopt _ l) as [l' | ] eqn:E; [ | discriminate H]; injection H; intros <-; simpl; clear H.
revert l' E; induction l as [ | [e b] l IH]; intros l' E; simpl in E; [injection E; intros <-; reflexivity | ].
destruct e as [ft | ag ft | g la]; simpl in E; try discriminate E.
destruct (lopt _ l) as [l2 | ]; [ | discriminate E]; injection E; intros <-; simpl; rewrite has_agg_ft; exact (IH l2 eq_refl).
Qed.

Notation eq0 := (eval_squery ORN O basesort instance nil nil).

Lemma flat_filter : forall c (M : list (tuple T)), (forall t, er nil (slice_t T relname t :: nil) c = false) ->
  flat_map (fun t => if row_error O t || er nil (slice_t T relname t :: nil) c then err_row O t :: nil
                     else if is_true3 T (ec nil (slice_t T relname t :: nil) c) then t :: nil else nil) M =
  filter (fun t => is_true3 T (ec nil (slice_t T relname t :: nil) c)) M.
Proof.
intros c M Hc; induction M as [ | t M IH]; [reflexivity | ].
cbn [flat_map filter]; rewrite row_error_false, Hc; cbn [orb].
destruct (is_true3 T _); [cbn [app]; f_equal | ]; exact IH.
Qed.

Lemma where_eq : forall q' c, (forall t, er nil (slice_t T relname t :: nil) c = false) ->
  where_rows ORN O basesort instance nil nil (Fr_Query q' (Ren_Star T) :: nil) c =
  filter (fun t => is_true3 T (ec nil (slice_t T relname t :: nil) c)) (map (join_tuple T (empty_tuple T)) (eq0 q')).
Proof.
intros q' c Hc; unfold where_rows; cbn [map fold_left]; rewrite keep_errors_id; unfold cross_product.
cbn [flat_map app]; rewrite app_nil_r, flat_filter by exact Hc; f_equal; f_equal.
change (eval_sfrom ORN O basesort instance nil nil (Fr_Query q' (Ren_Star T))) with
  (map (fun t => let t' := SqlFull.rename_tuple O (Ren_Star T) t in
                 if row_error O t && negb (row_error O t') then err_row O t' else t') (eq0 q')).
cbv zeta; cbn [SqlFull.rename_tuple]; rewrite <- (List.map_id (eq0 q')) at 2.
apply map_ext; intro t; rewrite row_error_false; reflexivity.
Qed.

Lemma gp_eq : forall gk rv rows, (forall t, gk t = nil) ->
  grouping_part (relname := relname) O (G_Fine T relname) gk rv false rows = map (fun t => (t :: nil, nil)) rows.
Proof.
intros gk rv rows H; unfold grouping_part; cbv zeta; cbn iota beta.
rewrite !List.map_map; apply map_ext; intro t; rewrite H; reflexivity.
Qed.

Lemma true_is_true : is_true3 T (Bool.true (B T)) = true.
Proof. unfold is_true3; apply Bool.true_is_true_alt. Qed.

Lemma sr_eq : forall sa s' rows,
  map (@fst _ _) (select_rest ORN O basesort instance nil nil sa Set_All s' (C_True T relname)
                              (map (fun t => (t :: nil, nil)) rows)) = map (row_of nil s') rows.
Proof.
intros sa s' rows; unfold select_rest; cbv zeta.
induction rows as [ | t rows IH]; [reflexivity | ].
cbn [map filter fst snd].
replace (er nil (slice_gs sa (t :: nil) nil :: nil) (C_True T relname)) with false by reflexivity.
replace (ec nil (slice_gs sa (t :: nil) nil :: nil) (C_True T relname)) with (Bool.true (B T)) by reflexivity.
cbn [slice_gs existsb]; rewrite row_error_false, true_is_true; cbn [orb map fst]; f_equal; try exact IH; destruct s'; reflexivity.
Qed.

Lemma full_select_rows : forall q' s' c, (forall t, er nil (slice_t T relname t :: nil) c = false) ->
  sselect_has_agg ORN basesort nil (Fset.Union (A T) (map (sfrom_sort ORN basesort nil) (Fr_Query q' (Ren_Star T) :: nil))) s' = false ->
  eq0 (SQ_Select (Select Set_All s' (Fr_Query q' (Ren_Star T) :: nil) c (G_Fine T relname) (C_True T relname))) =
  map (row_of nil s') (filter (fun t => is_true3 T (ec nil (slice_t T relname t :: nil) c))
                             (map (join_tuple T (empty_tuple T)) (eq0 q'))).
Proof.
intros q' s' c Hc Ha.
change (eq0 (SQ_Select _)) with (map (@fst _ _) (eval_sspec ORN O basesort instance nil nil
           (Select Set_All s' (Fr_Query q' (Ren_Star T) :: nil) c (G_Fine T relname) (C_True T relname)) nil)).
rewrite eval_select; cbv zeta.
replace (implicit_group ORN basesort nil _ s' (C_True T relname) nil) with false
  by (unfold implicit_group; rewrite Ha; reflexivity).
rewrite gp_eq by reflexivity.
rewrite where_eq by exact Hc.
apply sr_eq.
Qed.

(** * The bags *)

Notation permT := (Oeset.permut (OTuple T)).

Lemma nj_one : forall l, N_join_list (tuple T) (join_tuple T) (empty_tuple T) (l :: nil) =
                         map (fun x => join_tuple T x (empty_tuple T)) l.
Proof. intro l; induction l as [ | x l IH]; [reflexivity | simpl; f_equal; exact IH]. Qed.

Lemma permut_map_compat : forall (F G : tuple T -> tuple T) l1 l2, permT l1 l2 ->
  (forall x y, x =t= y -> F x =t= G y) -> permT (map F l1) (map G l2).
Proof. intros F G l1 l2 H K; apply (_permut_map (R := fun x y => x =t= y)); [intros; apply K; assumption | exact H]. Qed.

Lemma permut_filter_compat : forall (p q : tuple T -> bool) l1 l2, permT l1 l2 ->
  (forall x y, x =t= y -> p x = q y) -> permT (filter p l1) (filter q l2).
Proof. intros p q l1 l2 H K; apply permut_filter_eq; [intros; apply K; assumption | exact H]. Qed.

Lemma bag_equal_permut : forall b1 b2, Febag.equal BTupleT b1 b2 = true -> permT (Febag.elements BTupleT b1) (Febag.elements BTupleT b2).
Proof.
intros b1 b2 H; apply Oeset.nb_occ_permut; intro x; rewrite <- !Febag.nb_occ_elements.
rewrite Febag.nb_occ_equal in H; apply H.
Qed.

Lemma elements_mk_bag_permut : forall l, permT (Febag.elements BTupleT (Febag.mk_bag BTupleT l)) l.
Proof. intro l; apply Oeset.nb_occ_permut; intro x; rewrite <- Febag.nb_occ_elements, Febag.nb_occ_mk_bag; reflexivity. Qed.

Lemma elements_filter_permut : forall (p : tuple T -> bool) b, (forall x y, x =t= y -> p x = p y) ->
  permT (Febag.elements BTupleT (Febag.filter BTupleT p b)) (filter p (Febag.elements BTupleT b)).
Proof.
intros p b K; apply Oeset.nb_occ_permut; intro x; rewrite <- Febag.nb_occ_elements.
rewrite Febag.nb_occ_filter; [ | intros e e' _ E; apply K; exact E].
rewrite Febag.nb_occ_elements, Oeset.nb_occ_filter; [destruct (p x); [rewrite N.mul_1_r | rewrite N.mul_0_r]; reflexivity | ].
intros e e' _ E; apply K; exact E.
Qed.

Theorem select_agree : forall unknown cn q q' s s' f c,
  Febag.equal BTupleT (Febag.mk_bag BTupleT (eq0 q')) (eval_sql_query basesort instance unknown cn nil q) = true ->
  s_to s = Some s' -> f_to f = Some c ->
  Febag.equal BTupleT
    (Febag.mk_bag BTupleT (eq0 (SQ_Select (Select Set_All s' (Fr_Query q' (Ren_Star T) :: nil) c (G_Fine T relname) (C_True T relname)))))
    (eval_sql_query basesort instance unknown cn nil
       (Sql_Select s (From_Item q (Att_Ren_Star T) :: nil) f (Group_Fine T) (Sql_True T (sql_query T relname)))) = true.
Proof.
intros unknown cn q q' s s' f c Hq Hs Hf.
rewrite full_select_rows.
2: { intro t; exact (proj2 (f_agree unknown cn (eval_sql_query basesort instance unknown cn) nil t f c Hf)). }
2: { apply (s_no_agg nil _ s s' Hs). }
rewrite eval_sql_query_unfold; cbv zeta.
rewrite Febag.nb_occ_equal; intro u; rewrite !Febag.nb_occ_mk_bag; apply Oeset.permut_nb_occ.
set (W := fun t => Bool.is_true (B T) (eval_sql_formula unknown cn (eval_sql_query basesort instance unknown cn) (env_t T nil t) f)).
assert (Wc : forall x y, x =t= y -> W x = W y) by (intros x y E; unfold W; rewrite (f_compat unknown cn _ f c x y Hf E); reflexivity).
set (PROJ := fun t => projection T (env_t T nil t) s).
assert (Pc : forall x y, x =t= y -> PROJ x =t= PROJ y) by (intros x y E; apply projection_eq, env_t_eq_2, E).
(* the side of [SqlFull.v] is the side of [Sql.v] on the rows of [q'] *)
apply (Oeset.permut_trans (l2 := map PROJ (filter W (map (fun x => join_tuple T x (empty_tuple T)) (eq0 q'))))).
- generalize (eq0 q'); intro L; induction L as [ | t L IH]; [apply Oeset.permut_refl | ].
  assert (J : join_tuple T (empty_tuple T) t =t= join_tuple T t (empty_tuple T))
    by (eapply Oeset.compare_eq_trans; [apply join_tuple_empty_1 | apply Oeset.compare_eq_sym, join_tuple_empty_2]).
  assert (E : is_true3 T (ec nil (slice_t T relname (join_tuple T (empty_tuple T) t) :: nil) c) =
              W (join_tuple T t (empty_tuple T))).
  { rewrite (proj1 (f_agree unknown cn (eval_sql_query basesort instance unknown cn) nil _ f c Hf)); apply Wc; exact J. }
  cbn [map filter]; rewrite E; destruct (W _); [ | exact IH].
  cbn [map]; apply Oeset.permut_cons; [ | exact IH].
  eapply Oeset.compare_eq_trans; [apply row_agree; exact Hs | apply Pc; exact J].
- (* the side of [Sql.v] *)
  apply Oeset.permut_sym.
  set (NB := N_join_bag T (map (eval_sql_from_item basesort instance unknown cn nil) (From_Item q (Att_Ren_Star T) :: nil))).
  set (E := Febag.elements BTupleT (Febag.filter BTupleT W NB)).
  match goal with |- permT (map ?F (filter ?P (make_groups T nil ?E0 (Group_Fine T)))) _ =>
    assert (EQ : forall L, map F (filter P (make_groups T nil L (Group_Fine T))) = map PROJ L);
    [ intro L; unfold make_groups; cbn [eval_sql_formula]; rewrite Bool.true_is_true_alt; clear;
      induction L as [ | t L IH]; [reflexivity | ];
      cbn [map filter]; rewrite IH;
      f_equal; unfold PROJ, env_g, env_t; rewrite quicksort_1; reflexivity
    | rewrite EQ ] end.
  apply permut_map_compat; [ | exact Pc].
  unfold E; eapply Oeset.permut_trans; [apply elements_filter_permut; exact Wc | ].
  apply permut_filter_compat; [ | exact Wc].
  unfold NB, N_join_bag; cbn [map]; eapply Oeset.permut_trans; [apply elements_mk_bag_permut | ].
  rewrite nj_one; apply permut_map_compat; [ | intros x y Exy; apply join_tuple_eq; [exact Exy | apply Oeset.compare_eq_refl]].
  cbn [eval_sql_from_item]; rewrite Febag.map_unfold; eapply Oeset.permut_trans; [apply elements_mk_bag_permut | ].
  rewrite (map_ext _ (fun t => t)) by (intro t; cbn [att_renaming_item_to_from_item projection env_t]; rewrite quicksort_1; reflexivity).
  rewrite List.map_id; apply Oeset.permut_trans with (Febag.elements BTupleT (Febag.mk_bag BTupleT (eq0 q'))).
  + apply bag_equal_permut; rewrite Febag.nb_occ_equal in Hq |- *; intro x; symmetry; apply Hq.
  + apply elements_mk_bag_permut.
Qed.

(** * Products of several [FROM] items *)

Notation JT := (join_tuple T).
Notation ET := (empty_tuple T).

Lemma join_eq_l : forall x1 x2 x, x1 =t= x2 -> JT x1 x =t= JT x2 x.
Proof. intros; apply join_tuple_eq; [assumption | apply Oeset.compare_eq_refl]. Qed.

Lemma join_eq_r : forall x x1 x2, x1 =t= x2 -> JT x x1 =t= JT x x2.
Proof. intros; apply join_tuple_eq; [apply Oeset.compare_eq_refl | assumption]. Qed.

Definition F2t := Forall2 (fun x y : tuple T => x =t= y).

Lemma F2t_permut : forall l1 l2, F2t l1 l2 -> permT l1 l2.
Proof. intros l1 l2 H; induction H; [apply Oeset.permut_refl | apply Oeset.permut_cons; assumption]. Qed.

Lemma F2t_flat_map : forall (X Y : Type) (f : X -> list (tuple T)) (g : Y -> list (tuple T)) l1 l2,
  Forall2 (fun x y => F2t (f x) (g y)) l1 l2 -> F2t (flat_map f l1) (flat_map g l2).
Proof.
intros X Y f g l1 l2 H; induction H as [ | x y l1 l2 Hxy H IH]; [constructor | simpl].
induction Hxy; simpl; [exact IH | constructor; assumption].
Qed.

Lemma F2t_refl : forall l, F2t l l.
Proof. intro l; induction l; constructor; [apply Oeset.compare_eq_refl | assumption]. Qed.

Lemma F2t_map : forall (X : Type) (f g : X -> tuple T) l, (forall x, f x =t= g x) -> F2t (map f l) (map g l).
Proof. intros X f g l H; induction l; constructor; auto. Qed.

Lemma F2t_app : forall l1 l2 l1' l2', F2t l1 l2 -> F2t l1' l2' -> F2t (l1 ++ l1') (l2 ++ l2').
Proof. intros l1 l2 l1' l2' H K; induction H; simpl; [exact K | constructor; assumption]. Qed.

Lemma F2t_trans : forall l1 l2 l3, F2t l1 l2 -> F2t l2 l3 -> F2t l1 l3.
Proof.
intros l1 l2 l3 H; revert l3; induction H as [ | x y l1 l2 Hxy H IH]; intros l3 K; inversion K; subst; constructor.
- eapply Oeset.compare_eq_trans; eassumption.
- apply IH; assumption.
Qed.

Lemma cross_app : forall l1 l2 M, cross_product T (l1 ++ l2) M = cross_product T l1 M ++ cross_product T l2 M.
Proof. intros; unfold cross_product; apply flat_map_app. Qed.

Lemma cross_assoc_one : forall a l M,
  F2t (cross_product T (map (JT a) l) M) (map (JT a) (flat_map (fun x => map (JT x) M) l)).
Proof.
intros a l M; induction l as [ | x l IH]; [constructor | ]; cbn [map flat_map]; unfold cross_product in *; cbn [flat_map].
rewrite map_app; apply F2t_app; [ | exact IH].
rewrite map_map; apply F2t_map; intro m; apply Oeset.compare_eq_sym, join_tuple_assoc.
Qed.

Lemma filter_true_id : forall (X : Type) (l : list X), filter (fun _ => true) l = l.
Proof. intros X l; induction l as [ | x l IH]; [reflexivity | simpl; rewrite IH; reflexivity]. Qed.

(** the product of [SqlFull.v] (on the left) and the one of [Sql.v] (on the right) list the same combinations *)
Lemma prod_F2 : forall Ls acc,
  F2t (fold_left (fun l1 l2 => cross_product T l1 l2) Ls acc) (cross_product T acc (N_join_list (tuple T) JT ET Ls)).
Proof.
intro Ls; induction Ls as [ | l Ls IH]; intro acc; simpl.
- unfold cross_product; induction acc as [ | a acc IHa]; [constructor | simpl].
  constructor; [apply Oeset.compare_eq_sym, join_tuple_empty_2 | exact IHa].
- eapply F2t_trans; [apply IH | ].
  rewrite brute_left_join_list_unfold, theta_join_list_unfold; unfold d_join_list.
  set (M := N_join_list (tuple T) JT ET Ls); clearbody M.
  rewrite (flat_map_ext _ (fun x1 => map (JT x1) M)) by (intro; rewrite filter_true_id; reflexivity).
  induction acc as [ | a acc IHa]; [constructor | ].
  change (cross_product T (a :: acc) l) with (map (JT a) l ++ cross_product T acc l).
  rewrite cross_app; unfold cross_product at 3; cbn [flat_map]; fold (cross_product T acc).
  apply F2t_app; [apply cross_assoc_one | exact IHa].
Qed.

Lemma prod_permut : forall Ls, permT (fold_left (fun l1 l2 => cross_product T l1 l2) Ls (ET :: nil)) (N_join_list (tuple T) JT ET Ls).
Proof.
intro Ls; apply F2t_permut; eapply F2t_trans; [apply prod_F2 | ].
unfold cross_product; cbn [flat_map]; rewrite app_nil_r.
induction (N_join_list (tuple T) JT ET Ls) as [ | x l IH]; constructor; [apply join_tuple_empty_1 | exact IH].
Qed.

(** the product of [Sql.v] respects the permutations of its operands *)
Lemma N_join_permut : forall Ls Ls', Forall2 permT Ls Ls' ->
  permT (N_join_list (tuple T) JT ET Ls) (N_join_list (tuple T) JT ET Ls').
Proof.
intros Ls Ls' H; induction H as [ | l l' Ls Ls' Hl H IH]; [apply Oeset.permut_refl | ].
cbn [N_join_list]; rewrite !brute_left_join_list_unfold.
apply (theta_join_list_permut_eq (tuple T) (OTuple T) JT join_eq_l join_eq_r); [intros; reflexivity | exact Hl | exact IH].
Qed.

(** * Selections over several [FROM] items *)

Lemma fold_keep : forall Ls acc,
  fold_left (fun l1 l2 => keep_errors O (cross_product T l1 l2) (l1 ++ l2)) Ls acc =
  fold_left (fun l1 l2 => cross_product T l1 l2) Ls acc.
Proof. intro Ls; induction Ls as [ | l Ls IH]; intro acc; [reflexivity | simpl; rewrite keep_errors_id; apply IH]. Qed.

Lemma ef_star : forall q', eval_sfrom ORN O basesort instance nil nil (Fr_Query q' (Ren_Star T)) = eq0 q'.
Proof.
intro q'; change (eval_sfrom ORN O basesort instance nil nil (Fr_Query q' (Ren_Star T))) with
  (map (fun t => let t' := SqlFull.rename_tuple O (Ren_Star T) t in
                 if row_error O t && negb (row_error O t') then err_row O t' else t') (eq0 q')).
cbv zeta; cbn [SqlFull.rename_tuple]; rewrite <- (List.map_id (eq0 q')) at 2.
apply map_ext; intro t; rewrite row_error_false; reflexivity.
Qed.

Notation PROD qs' := (fold_left (fun l1 l2 => cross_product T l1 l2) (map eq0 qs') (ET :: nil)).

Lemma where_eq_n : forall qs' c, (forall t, er nil (slice_t T relname t :: nil) c = false) ->
  where_rows ORN O basesort instance nil nil (map (fun q' => Fr_Query q' (Ren_Star T)) qs') c =
  filter (fun t => is_true3 T (ec nil (slice_t T relname t :: nil) c)) (PROD qs').
Proof.
intros qs' c Hc; unfold where_rows; rewrite fold_keep, flat_filter by exact Hc; f_equal; f_equal.
rewrite map_map; apply map_ext; intro q'; apply ef_star.
Qed.

Lemma full_select_rows_n : forall qs' s' c, (forall t, er nil (slice_t T relname t :: nil) c = false) ->
  (forall sa, sselect_has_agg ORN basesort nil sa s' = false) ->
  eq0 (SQ_Select (Select Set_All s' (map (fun q' => Fr_Query q' (Ren_Star T)) qs') c (G_Fine T relname) (C_True T relname))) =
  map (row_of nil s') (filter (fun t => is_true3 T (ec nil (slice_t T relname t :: nil) c)) (PROD qs')).
Proof.
intros qs' s' c Hc Ha.
change (eq0 (SQ_Select _)) with (map (@fst _ _) (eval_sspec ORN O basesort instance nil nil
           (Select Set_All s' (map (fun q' => Fr_Query q' (Ren_Star T)) qs') c (G_Fine T relname) (C_True T relname)) nil)).
rewrite eval_select; cbv zeta.
replace (implicit_group ORN basesort nil _ s' (C_True T relname) nil) with false
  by (unfold implicit_group; rewrite Ha; reflexivity).
rewrite gp_eq by reflexivity.
rewrite where_eq_n by exact Hc.
apply sr_eq.
Qed.

Theorem select_agree_n : forall unknown cn qs qs' s s' f c,
  Forall2 (fun q q' => Febag.equal BTupleT (Febag.mk_bag BTupleT (eq0 q'))
                                   (eval_sql_query basesort instance unknown cn nil q) = true) qs qs' ->
  s_to s = Some s' -> f_to f = Some c ->
  Febag.equal BTupleT
    (Febag.mk_bag BTupleT (eq0 (SQ_Select (Select Set_All s' (map (fun q' => Fr_Query q' (Ren_Star T)) qs') c
                                                  (G_Fine T relname) (C_True T relname)))))
    (eval_sql_query basesort instance unknown cn nil
       (Sql_Select s (map (fun q => From_Item q (Att_Ren_Star T)) qs) f (Group_Fine T) (Sql_True T (sql_query T relname)))) = true.
Proof.
intros unknown cn qs qs' s s' f c Hq Hs Hf.
rewrite full_select_rows_n.
2: { intro t; exact (proj2 (f_agree unknown cn (eval_sql_query basesort instance unknown cn) nil t f c Hf)). }
2: { intro sa; apply (s_no_agg nil sa s s' Hs). }
rewrite eval_sql_query_unfold; cbv zeta.
rewrite Febag.nb_occ_equal; intro u; rewrite !Febag.nb_occ_mk_bag; apply Oeset.permut_nb_occ.
set (W := fun t => Bool.is_true (B T) (eval_sql_formula unknown cn (eval_sql_query basesort instance unknown cn) (env_t T nil t) f)).
assert (Wc : forall x y, x =t= y -> W x = W y) by (intros x y E; unfold W; rewrite (f_compat unknown cn _ f c x y Hf E); reflexivity).
set (PROJ := fun t => projection T (env_t T nil t) s).
assert (Pc : forall x y, x =t= y -> PROJ x =t= PROJ y) by (intros x y E; apply projection_eq, env_t_eq_2, E).
apply (Oeset.permut_trans (l2 := map PROJ (filter W (PROD qs')))).
- generalize (PROD qs'); intro L; induction L as [ | t L IH]; [apply Oeset.permut_refl | ].
  assert (E : is_true3 T (ec nil (slice_t T relname t :: nil) c) = W t)
    by (unfold W; rewrite (proj1 (f_agree unknown cn (eval_sql_query basesort instance unknown cn) nil t f c Hf)); reflexivity).
  cbn [map filter]; rewrite E; destruct (W t); [ | exact IH].
  cbn [map]; apply Oeset.permut_cons; [apply row_agree; exact Hs | exact IH].
- apply Oeset.permut_sym.
  match goal with |- permT (map ?F (filter ?P (make_groups T nil ?E0 (Group_Fine T)))) _ =>
    assert (EQ : forall L, map F (filter P (make_groups T nil L (Group_Fine T))) = map PROJ L);
    [ intro L; unfold make_groups; cbn [eval_sql_formula]; rewrite Bool.true_is_true_alt; clear;
      induction L as [ | t L IH]; [reflexivity | ];
      cbn [map filter]; rewrite IH;
      f_equal; unfold PROJ, env_g, env_t; rewrite quicksort_1; reflexivity
    | rewrite EQ ] end.
  apply permut_map_compat; [ | exact Pc].
  eapply Oeset.permut_trans; [apply elements_filter_permut; exact Wc | ].
  apply permut_filter_compat; [ | exact Wc].
  unfold N_join_bag; eapply Oeset.permut_trans; [apply elements_mk_bag_permut | ].
  apply Oeset.permut_sym; eapply Oeset.permut_trans; [apply prod_permut | ].
  apply N_join_permut; rewrite !map_map.
  induction Hq as [ | q q' qs qs' Hqq' Hq IH]; [constructor | constructor; [ | exact IH]].
  cbn [eval_sql_from_item]; rewrite Febag.map_unfold.
  apply Oeset.permut_sym; eapply Oeset.permut_trans; [apply elements_mk_bag_permut | ].
  rewrite (map_ext _ (fun t => t)) by (intro t; cbn [att_renaming_item_to_from_item projection env_t]; rewrite quicksort_1; reflexivity).
  rewrite List.map_id; apply Oeset.permut_trans with (Febag.elements BTupleT (Febag.mk_bag BTupleT (eq0 q'))).
  + apply bag_equal_permut; rewrite Febag.nb_occ_equal in Hqq' |- *; intro x; symmetry; apply Hqq'.
  + apply elements_mk_bag_permut.
Qed.

(** * Selections over renamed [FROM] items *)

(** a column which a tuple does not have has the default value of its type *)
Hypothesis Hdot : forall t a, Fset.mem (A T) a (labels T t) = false -> dot T t a = default_value T (type_of_attribute T a).

Definition ren_to (r : att_renaming_item T) : SqlFull.renaming T :=
  match r with
  | Att_Ren_Star _ => Ren_Star T
  | Att_Ren_List la => Ren_List T (map (fun x => match x with Att_As _ a b => (a, b) end) la)
  end.

Notation ef0 := (eval_sfrom ORN O basesort instance nil nil).
Notation PRODF lf' := (fold_left (fun l1 l2 => cross_product T l1 l2) (map ef0 lf') (ET :: nil)).

Lemma where_eq_g : forall lf' c, (forall t, er nil (slice_t T relname t :: nil) c = false) ->
  where_rows ORN O basesort instance nil nil lf' c =
  filter (fun t => is_true3 T (ec nil (slice_t T relname t :: nil) c)) (PRODF lf').
Proof. intros lf' c Hc; unfold where_rows; rewrite fold_keep, flat_filter by exact Hc; reflexivity. Qed.

Lemma full_select_rows_g : forall lf' s' c, (forall t, er nil (slice_t T relname t :: nil) c = false) ->
  (forall sa, sselect_has_agg ORN basesort nil sa s' = false) ->
  eq0 (SQ_Select (Select Set_All s' lf' c (G_Fine T relname) (C_True T relname))) =
  map (row_of nil s') (filter (fun t => is_true3 T (ec nil (slice_t T relname t :: nil) c)) (PRODF lf')).
Proof.
intros lf' s' c Hc Ha.
change (eq0 (SQ_Select _)) with (map (@fst _ _) (eval_sspec ORN O basesort instance nil nil
           (Select Set_All s' lf' c (G_Fine T relname) (C_True T relname)) nil)).
rewrite eval_select; cbv zeta.
replace (implicit_group ORN basesort nil _ s' (C_True T relname) nil) with false
  by (unfold implicit_group; rewrite Ha; reflexivity).
rewrite gp_eq by reflexivity.
rewrite where_eq_g by exact Hc.
apply sr_eq.
Qed.

Notation item_agree it it' :=
  (permT (ef0 it') (Febag.elements BTupleT (eval_sql_from_item basesort instance _ _ nil it))).

Theorem select_agree_g : forall unknown cn lf lf' s s' f c,
  Forall2 (fun it it' => permT (ef0 it') (Febag.elements BTupleT (eval_sql_from_item basesort instance unknown cn nil it))) lf lf' ->
  s_to s = Some s' -> f_to f = Some c ->
  Febag.equal BTupleT
    (Febag.mk_bag BTupleT (eq0 (SQ_Select (Select Set_All s' lf' c (G_Fine T relname) (C_True T relname)))))
    (eval_sql_query basesort instance unknown cn nil (Sql_Select s lf f (Group_Fine T) (Sql_True T (sql_query T relname)))) = true.
Proof.
intros unknown cn lf lf' s s' f c Hq Hs Hf.
rewrite full_select_rows_g.
2: { intro t; exact (proj2 (f_agree unknown cn (eval_sql_query basesort instance unknown cn) nil t f c Hf)). }
2: { intro sa; apply (s_no_agg nil sa s s' Hs). }
rewrite eval_sql_query_unfold; cbv zeta.
rewrite Febag.nb_occ_equal; intro u; rewrite !Febag.nb_occ_mk_bag; apply Oeset.permut_nb_occ.
set (W := fun t => Bool.is_true (B T) (eval_sql_formula unknown cn (eval_sql_query basesort instance unknown cn) (env_t T nil t) f)).
assert (Wc : forall x y, x =t= y -> W x = W y) by (intros x y E; unfold W; rewrite (f_compat unknown cn _ f c x y Hf E); reflexivity).
set (PROJ := fun t => projection T (env_t T nil t) s).
assert (Pc : forall x y, x =t= y -> PROJ x =t= PROJ y) by (intros x y E; apply projection_eq, env_t_eq_2, E).
apply (Oeset.permut_trans (l2 := map PROJ (filter W (PRODF lf')))).
- generalize (PRODF lf'); intro L; induction L as [ | t L IH]; [apply Oeset.permut_refl | ].
  assert (E : is_true3 T (ec nil (slice_t T relname t :: nil) c) = W t)
    by (unfold W; rewrite (proj1 (f_agree unknown cn (eval_sql_query basesort instance unknown cn) nil t f c Hf)); reflexivity).
  cbn [map filter]; rewrite E; destruct (W t); [ | exact IH].
  cbn [map]; apply Oeset.permut_cons; [apply row_agree; exact Hs | exact IH].
- apply Oeset.permut_sym.
  match goal with |- permT (map ?F (filter ?P (make_groups T nil ?E0 (Group_Fine T)))) _ =>
    assert (EQ : forall L, map F (filter P (make_groups T nil L (Group_Fine T))) = map PROJ L);
    [ intro L; unfold make_groups; cbn [eval_sql_formula]; rewrite Bool.true_is_true_alt; clear;
      induction L as [ | t L IH]; [reflexivity | ];
      cbn [map filter]; rewrite IH;
      f_equal; unfold PROJ, env_g, env_t; rewrite quicksort_1; reflexivity
    | rewrite EQ ] end.
  apply permut_map_compat; [ | exact Pc].
  eapply Oeset.permut_trans; [apply elements_filter_permut; exact Wc | ].
  apply permut_filter_compat; [ | exact Wc].
  unfold N_join_bag; eapply Oeset.permut_trans; [apply elements_mk_bag_permut | ].
  apply Oeset.permut_sym; eapply Oeset.permut_trans; [apply prod_permut | ].
  apply N_join_permut; induction Hq as [ | it it' lf lf' Hit Hq IH]; [constructor | constructor; [exact Hit | exact IH]].
Qed.

(** the items, unrenamed and renamed *)
Lemma item_star : forall unknown cn q q',
  Febag.equal BTupleT (Febag.mk_bag BTupleT (eq0 q')) (eval_sql_query basesort instance unknown cn nil q) = true ->
  permT (ef0 (Fr_Query q' (Ren_Star T)))
        (Febag.elements BTupleT (eval_sql_from_item basesort instance unknown cn nil (From_Item q (Att_Ren_Star T)))).
Proof.
intros unknown cn q q' Hq; rewrite ef_star.
cbn [eval_sql_from_item]; rewrite Febag.map_unfold.
apply Oeset.permut_sym; eapply Oeset.permut_trans; [apply elements_mk_bag_permut | ].
rewrite (map_ext _ (fun t => t)) by (intro t; cbn [att_renaming_item_to_from_item projection env_t]; rewrite quicksort_1; reflexivity).
rewrite List.map_id; apply Oeset.permut_trans with (Febag.elements BTupleT (Febag.mk_bag BTupleT (eq0 q'))).
- apply bag_equal_permut; rewrite Febag.nb_occ_equal in Hq |- *; intro x; symmetry; apply Hq.
- apply elements_mk_bag_permut.
Qed.

Lemma find_ren : forall (la : list (att_renaming T)) b,
  Oset.find (OAtt T) b (map (fun x => (snd x, fst x)) (map (fun x => match x with Att_As _ a b => (a, b) end) la)) =
  option_map (fun e => match e with A_Expr _ (F_Dot _ a) => a | _ => b end)
             (Oset.find (OAtt T) b (pairs_of_selects T (_Select_List T (map (fun y => match y with
                 | Att_As _ a b => Select_As T (A_Expr T (F_Dot T a)) b end) la)))).
Proof.
intros la b; induction la as [ | [a c] la IH]; [reflexivity | simpl].
unfold pairs_of_selects in IH |- *; simpl in IH |- *.
destruct (Oset.eq_bool (OAtt T) b c); [reflexivity | exact IH].
Qed.

Lemma ren_agree : forall la x,
  SqlFull.rename_tuple O (ren_to (Att_Ren_List la)) x =t=
  projection T (env_t T nil x) (att_renaming_item_to_from_item (Att_Ren_List la)).
Proof.
intros la x; cbn [ren_to SqlFull.rename_tuple att_renaming_item_to_from_item projection].
rewrite tuple_eq; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)), (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)).
  rewrite Fset.equal_spec; intro b; rewrite !Fset.mem_mk_set; f_equal.
  unfold sort_of_select_list; rewrite !map_map; apply map_ext; intros [a c]; reflexivity.
- intros b Hb; rewrite !dot_mk_tuple.
  rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Hb.
  assert (Hb' : Fset.mem (A T) b (Fset.mk_set (A T) (sort_of_select_list T (_Select_List T (map (fun y => match y with
                 | Att_As _ a b => Select_As T (A_Expr T (F_Dot T a)) b end) la)))) = true).
  { rewrite <- Hb, !Fset.mem_mk_set; f_equal; unfold sort_of_select_list; rewrite !map_map; apply map_ext; intros [a c]; reflexivity. }
  rewrite Hb, Hb', find_ren.
  destruct (Oset.find (OAtt T) b _) as [e | ] eqn:E.
  + assert (Ke : exists a, e = A_Expr T (F_Dot T a)).
    { clear - E; unfold pairs_of_selects in E; induction la as [ | [a c] la IH]; [discriminate E | ].
      simpl in E; destruct (Oset.eq_bool (OAtt T) b c); [injection E; intros <-; exists a; reflexivity | exact (IH E)]. }
    destruct Ke as [a ->]; cbn [option_map interp_aggterm interp_funterm interp_dot env_t]; unfold store.
    rewrite quicksort_1; destruct (is_null O (dot T x a)) eqn:N; [rewrite (Hnull b _ N) | ];
      (destruct (Fset.mem (A T) a (labels T x)) eqn:Ha; [reflexivity | apply Hdot; exact Ha]).
  + simpl; unfold default_tuple; rewrite dot_mk_tuple, Fset.empty_spec; reflexivity.
Qed.

Lemma item_ren : forall unknown cn q q' la,
  Febag.equal BTupleT (Febag.mk_bag BTupleT (eq0 q')) (eval_sql_query basesort instance unknown cn nil q) = true ->
  permT (ef0 (Fr_Query q' (ren_to (Att_Ren_List la))))
        (Febag.elements BTupleT (eval_sql_from_item basesort instance unknown cn nil (From_Item q (Att_Ren_List la)))).
Proof.
intros unknown cn q q' la Hq.
change (ef0 (Fr_Query q' (ren_to (Att_Ren_List la)))) with
  (map (fun t => let t' := SqlFull.rename_tuple O (ren_to (Att_Ren_List la)) t in
                 if row_error O t && negb (row_error O t') then err_row O t' else t') (eq0 q')).
cbv zeta; rewrite (map_ext _ (SqlFull.rename_tuple O (ren_to (Att_Ren_List la)))) by (intro t; rewrite row_error_false; reflexivity).
cbn [eval_sql_from_item]; rewrite Febag.map_unfold.
apply Oeset.permut_sym; eapply Oeset.permut_trans; [apply elements_mk_bag_permut | ]; apply Oeset.permut_sym.
apply permut_map_compat.
- apply Oeset.permut_trans with (Febag.elements BTupleT (Febag.mk_bag BTupleT (eq0 q'))).
  + apply Oeset.permut_sym, elements_mk_bag_permut.
  + apply bag_equal_permut; exact Hq.
- intros x y Exy; eapply Oeset.compare_eq_trans; [apply ren_agree | apply projection_eq, env_t_eq_2, Exy].
Qed.


(** * Grouping and aggregates *)

Fixpoint at_to2 (t : aggterm T) : sexpr :=
  match t with
  | A_Expr _ ft => ft_to ft
  | A_agg _ ag ft => E_Agg ag Set_All (ft_to ft) (C_True T relname)
  | A_fun _ f l => E_Fun f (map at_to2 l)
  end.

(** a term of a grouped block: outside the aggregates, built on the grouping terms; inside, on the columns
    of the [FROM] clause *)
Fixpoint gcheck (S : Fset.set (A T)) (keys : list (funterm T)) (t : aggterm T) : bool :=
  match t with
  | A_Expr _ ft => is_built_upon_ft T keys ft
  | A_agg _ _ ft => Fset.subset (A T) (variables_ft T ft) S
  | A_fun _ _ l => forallb (gcheck S keys) l
  end.

Lemma ft_agree_s : forall ce sa t rest ft, sa =S= labels T t ->
  ev ce ((sa, t :: rest, nil) :: nil) (ft_to ft) = interp_funterm T (env_t T nil t) ft.
Proof.
intros ce sa t rest ft Hs; revert ft; fix IH 1; intros [c | a | f l].
- cbn; apply Hconst.
- cbn [eval_sexpr ft_to interp_funterm]; unfold is_hidden; cbn [lookup interp_dot env_t].
  rewrite quicksort_one, (Fset.mem_eq_2 _ _ _ Hs); destruct (a inS? labels T t); reflexivity.
- cbn [ft_to interp_funterm]; change (ev ce ((sa, t :: rest, nil) :: nil) (E_Fun f (map ft_to l))) with
    (if is_hidden ((sa, t :: rest, nil) :: nil) (E_Fun f (map ft_to l)) then null O
     else let vs := map (ev ce ((sa, t :: rest, nil) :: nil)) (map ft_to l) in
          match first_error O (if lazy_symbol O f then firstn 1 vs else vs) with
          | Some err => err | None => interp_fun O f vs end).
  replace (is_hidden ((sa, t :: rest, nil) :: nil) (E_Fun f (map ft_to l))) with false by reflexivity.
  cbv zeta; rewrite first_error_none, Hfun, map_map; f_equal.
  induction l as [ | x l IHl]; [reflexivity | simpl; rewrite IH, IHl; reflexivity].
Qed.

Lemma itf_slice : forall sa gb l t0 r ft, quicksort (OTuple T) l = t0 :: r ->
  interp_funterm T ((sa, gb, l) :: nil) ft = interp_funterm T (env_t T nil t0) ft.
Proof.
intros sa gb l t0 r ft Hq; revert ft; fix IH 1; intros [c | a | f la]; [reflexivity | | ].
- cbn [interp_funterm interp_dot env_t]; rewrite Hq, quicksort_1; reflexivity.
- cbn [interp_funterm]; f_equal; induction la as [ | x la IHl]; [reflexivity | simpl; rewrite IH, IHl; reflexivity].
Qed.

Lemma map_in_eq : forall (X Y : Type) (f h : X -> Y) l x, In x l -> map f l = map h l -> f x = h x.
Proof.
intros X Y f h l x; induction l as [ | y l IH]; intros I E; [contradiction I | ].
simpl in E; injection E; intros E2 E1; destruct I as [<- | I]; [exact E1 | exact (IH I E2)].
Qed.

Lemma built_const : forall (g : list (aggterm T)) t u,
  map (interp_aggterm T (env_t T nil t)) g = map (interp_aggterm T (env_t T nil u)) g ->
  forall ft, is_built_upon_ft T (extract_funterms T g) ft = true ->
  interp_funterm T (env_t T nil t) ft = interp_funterm T (env_t T nil u) ft.
Proof.
intros g t u Hk.
assert (K : forall ft, In ft (extract_funterms T g) -> interp_funterm T (env_t T nil t) ft = interp_funterm T (env_t T nil u) ft).
{ intros ft I; rewrite in_extract_funterms in I; exact (map_in_eq _ _ _ _ _ _ I Hk). }
fix IH 1; intros [c | a | f l] H; [reflexivity | | ].
- simpl in H; apply K; rewrite Oset.mem_bool_true_iff in H; exact H.
- simpl in H; apply orb_true_iff in H; destruct H as [H | H].
  + apply K; rewrite Oset.mem_bool_true_iff in H; exact H.
  + cbn [interp_funterm]; f_equal; induction l as [ | x l IHl]; [reflexivity | ].
    simpl in H; apply andb_true_iff in H; simpl; rewrite (IH x (proj1 H)), (IHl (proj2 H)); reflexivity.
Qed.

Lemma built_vars : forall (sa : Fset.set (A T)) ft, variables_ft T ft subS sa ->
  is_built_upon_ft T (map (F_Dot T) ({{{sa}}})) ft = true.
Proof.
intro sa; fix IH 1; intros [c | a | f l] H; [reflexivity | | ].
- simpl; rewrite Oset.mem_bool_true_iff, in_map_iff; exists a; split; [reflexivity | ].
  apply Fset.mem_in_elements; rewrite Fset.subset_spec in H; apply H; simpl; rewrite Fset.singleton_spec, Oset.eq_bool_refl; reflexivity.
- assert (H' : forall x, In x l -> variables_ft T x subS sa).
  { intros x Hx; rewrite Fset.subset_spec in H |- *; intros b Hb; apply H; simpl; rewrite Fset.mem_Union.
    exists (variables_ft T x); split; [apply in_map; exact Hx | exact Hb]. }
  clear H; simpl; apply orb_true_iff; right.
  induction l as [ | y l IHl]; [reflexivity | ]; simpl; rewrite (IH y (H' y (or_introl eq_refl))).
  apply IHl; intros x Hx; apply H'; right; exact Hx.
Qed.


Hypothesis Hagg : forall ag l, interp_agg O ag l = interp_aggregate T ag l.
Hypothesis Hperm : forall ag l1 l2, Permutation l1 l2 -> interp_aggregate T ag l1 = interp_aggregate T ag l2.

Lemma extract_dots : forall l, extract_funterms T (map (fun a => A_Expr T (F_Dot T a)) l ++ nil) = map (F_Dot T) l.
Proof. intro l; induction l as [ | a l IH]; [reflexivity | simpl; f_equal; exact IH]. Qed.

Lemma agg_sql : forall sa0 gb k t0 r ag ft, quicksort (OTuple T) k = t0 :: r -> variables_ft T ft subS sa0 ->
  interp_aggterm T ((sa0, gb, k) :: nil) (A_agg T ag ft) =
  interp_aggregate T ag (map (fun t => interp_funterm T (env_t T nil t) ft) (quicksort (OTuple T) k)).
Proof.
intros sa0 gb k t0 r ag ft Hq Hv.
assert (L : interp_aggregate T ag
              (map (fun e => interp_funterm T e ft)
                 match Some ((sa0, gb, k) :: nil) with
                 | Some (slc1 :: env'') => map (fun slc => slc :: env'') (unfold_env_slice T slc1)
                 | _ => nil end) =
            interp_aggregate T ag (map (fun t => interp_funterm T (env_t T nil t) ft) (quicksort (OTuple T) k))).
{ cbn [unfold_env_slice]; rewrite !map_map; f_equal; apply map_ext; intro t.
  apply (itf_slice sa0 (Group_Fine T) (t :: nil) t nil ft (quicksort_1 _ t)). }
cbn [interp_aggterm]; destruct (Fset.is_empty (A T) (variables_ft T ft)) eqn:E; [exact L | ].
cbn [find_eval_env].
replace (is_built_upon_ag T nil (A_agg T ag ft)) with false.
2: { symmetry; cbn [is_built_upon_ag extract_funterms]; rewrite Oset.mem_bool_unfold; cbn [orb].
     destruct (is_built_upon_ft T nil ft) eqn:B; [ | reflexivity].
     apply is_built_upon_ft_variables_ft_sub in B; rewrite <- E; symmetry.
     rewrite Fset.is_empty_spec, Fset.equal_spec; intro b; rewrite Fset.empty_spec.
     rewrite Fset.subset_spec in B; destruct (b inS? variables_ft T ft) eqn:Hb; [ | reflexivity].
     generalize (B b Hb); simpl; rewrite Fset.empty_spec; discriminate. }
match goal with |- context [is_a_suitable_env T sa0 ?e ?f] =>
  replace (is_a_suitable_env T sa0 e f) with true; [exact L | ] end.
symmetry; unfold is_a_suitable_env; cbn [is_built_upon_ag flat_map]; rewrite extract_dots, built_vars by exact Hv.
apply orb_true_r.
Qed.

Lemma agg_full : forall ce t1 rest ag ft, (forall t, In t (t1 :: rest) -> labels T t1 =S= labels T t) ->
  ev ce ((labels T t1, t1 :: rest, nil) :: nil) (E_Agg ag Set_All (ft_to ft) (C_True T relname)) =
  interp_aggregate T ag (map (fun t => interp_funterm T (env_t T nil t) ft) (t1 :: rest)).
Proof.
intros ce t1 rest ag ft Hl.
cbn [eval_sexpr]; unfold is_hidden; cbv iota.
unfold agg_env; cbn [agg_env_rec].
assert (R0 : forall l, existsb (row_error O) l = false)
  by (intro l; induction l as [ | x l IH]; [reflexivity | simpl; rewrite row_error_false; exact IH]).
assert (F0 : forall l : list (tuple T), existsb (fun _ => false) l = false)
  by (intro l; induction l as [ | x l IH]; [reflexivity | exact IH]).
destruct (existsb (fun a : attribute T => a inS? labels T t1) _); cbv iota;
rewrite R0, F0; cbn [orb]; cbv iota beta;
rewrite (filter_ext_in _ (fun _ => true)) by (intros; apply true_is_true);
rewrite first_error_none; cbn [quantify]; rewrite Hagg; f_equal;
replace (filter (fun _ : tuple T => true) (t1 :: rest)) with (t1 :: rest)
  by (clear; induction (t1 :: rest) as [ | x l IH]; [reflexivity | simpl; f_equal; exact IH]);
apply map_ext_in; intros t It; apply ft_agree_s; exact (Hl t It).
Qed.


Lemma permut_eq_Permutation : forall (X : Type) (l1 l2 : list X), _permut (@eq X) l1 l2 -> Permutation l1 l2.
Proof.
intros X l1 l2 H; induction H as [ | a b l l1 l2 E H IH]; [constructor | subst b].
eapply perm_trans; [apply perm_skip, IH | apply Permutation_middle].
Qed.

Lemma at_agree_g : forall S g k t0 r t1 rest,
  quicksort (OTuple T) k = t0 :: r -> rev k = t1 :: rest ->
  (forall t, In t k -> labels T t =S= S) ->
  (forall t u, In t k -> In u k ->
     map (interp_aggterm T (env_t T nil t)) g = map (interp_aggterm T (env_t T nil u)) g) ->
  forall x, gcheck S (extract_funterms T g) x = true ->
  interp_aggterm T ((labels T t0, Group_By T g, k) :: nil) x = ev nil ((labels T t1, t1 :: rest, nil) :: nil) (at_to2 x).
Proof.
intros S g k t0 r t1 rest Hq Hr Hl Hk.
assert (I0 : In t0 k) by (apply (proj2 (In_quicksort (OTuple T) k t0)); rewrite Hq; left; reflexivity).
assert (I1 : In t1 k) by (apply (proj2 (in_rev k t1)); rewrite Hr; left; reflexivity).
fix IH 1; intros [ft | ag ft | f l] H.
- cbn [interp_aggterm at_to2]; rewrite (itf_slice _ _ _ t0 r ft Hq), (ft_agree_s nil (labels T t1) t1 rest ft (Fset.equal_refl _ _)).
  exact (built_const g t0 t1 (Hk t0 t1 I0 I1) ft H).
- cbn [at_to2]; simpl in H; rewrite (agg_sql _ _ _ t0 r ag ft Hq).
  2: { rewrite Fset.subset_spec in H |- *; intros b Hb; rewrite (Fset.mem_eq_2 _ _ _ (Hl t0 I0)); apply H; exact Hb. }
  rewrite agg_full.
  2: { intros t It; rewrite <- Hr, <- in_rev in It.
       rewrite (Fset.equal_eq_1 _ _ _ _ (Hl t1 I1)), (Fset.equal_eq_2 _ _ _ _ (Hl t It)); apply Fset.equal_refl. }
  apply Hperm, Permutation_map; rewrite <- Hr.
  eapply perm_trans; [apply Permutation_sym, permut_eq_Permutation, quick_permut_strong | apply Permutation_rev].
- cbn [interp_aggterm at_to2]; change (ev nil ((labels T t1, t1 :: rest, nil) :: nil) (E_Fun f (map at_to2 l))) with
    (if is_hidden ((labels T t1, t1 :: rest, nil) :: nil) (E_Fun f (map at_to2 l)) then null O
     else let vs := map (ev nil ((labels T t1, t1 :: rest, nil) :: nil)) (map at_to2 l) in
          match first_error O (if lazy_symbol O f then firstn 1 vs else vs) with
          | Some err => err | None => interp_fun O f vs end).
  replace (is_hidden ((labels T t1, t1 :: rest, nil) :: nil) (E_Fun f (map at_to2 l))) with false by reflexivity.
  cbv zeta; rewrite first_error_none, Hfun, map_map; f_equal.
  simpl in H; induction l as [ | x l IHl]; [reflexivity | ].
  simpl in H; apply andb_true_iff in H; simpl; rewrite (IH x (proj1 H)), (IHl (proj2 H)); reflexivity.
Qed.

Notation item_row F := (fun x => match x with Select_As _ e b => (b, ev nil F (at_to2 e)) end).

Lemma find_items : forall (E : env T) F (items : list (select T)) a,
  (forall e b, In (Select_As T e b) items -> ev nil F (at_to2 e) = interp_aggterm T E e) ->
  Oset.find (OAtt T) a (map (item_row F) items) =
  option_map (interp_aggterm T E) (Oset.find (OAtt T) a (pairs_of_selects T (_Select_List T items))) /\
  map (@fst _ _) (map (item_row F) items) = sort_of_select_list T (_Select_List T items).
Proof.
intros E F items a; induction items as [ | [e b] items IH]; intro H; [split; reflexivity | ].
destruct IH as [K1 K2]; [intros e1 b1 I; apply (H e1 b1); right; exact I | ].
simpl; split; [ | f_equal; exact K2].
unfold pairs_of_selects in K1; simpl in K1 |- *.
destruct (Oset.eq_bool (OAtt T) a b); [simpl; f_equal; apply (H e b); left; reflexivity | exact K1].
Qed.

Lemma row_agree_gen : forall (E : env T) F (items : list (select T)),
  (forall e b, In (Select_As T e b) items -> ev nil F (at_to2 e) = interp_aggterm T E e) ->
  mk_row O (map (item_row F) items) =t= projection T E (Select_List T (_Select_List T items)).
Proof.
intros E F items H; cbn [projection].
unfold mk_row; rewrite tuple_eq; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)), (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)).
  rewrite (proj2 (find_items E F items (err_attr O) H)); apply Fset.equal_refl.
- intros a Ha; rewrite !dot_mk_tuple.
  rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
  rewrite (proj2 (find_items E F items a H)) in Ha |- *; rewrite Ha.
  rewrite (proj1 (find_items E F items a H)).
  destruct (Oset.find (OAtt T) a (pairs_of_selects T (_Select_List T items))) as [e | ]; simpl; [ | unfold default_tuple; rewrite dot_mk_tuple, Fset.empty_spec; reflexivity].
  unfold store; destruct (is_null O _) eqn:N; [apply Hnull; exact N | reflexivity].
Qed.


Definition item_to (x : select T) : sitem T relname := match x with Select_As _ e a => S_As (at_to2 e) a end.

Notation gk lg' := (fun t => map (ev nil (slice_t T relname t :: nil)) lg').

Lemma sr_eq_g : forall sa items G,
  map (@fst _ _) (select_rest ORN O basesort instance nil nil sa Set_All (S_List (map item_to items)) (C_True T relname)
                              (map (fun grp => (grp, nil)) G)) =
  map (fun grp => mk_row O (map (item_row (slice_gs sa grp nil :: nil)) items)) G.
Proof.
intros sa items G; unfold select_rest; cbv zeta.
induction G as [ | grp G IH]; [reflexivity | ].
cbn [map filter fst snd].
replace (er nil (slice_gs sa grp nil :: nil) (C_True T relname)) with false by reflexivity.
replace (ec nil (slice_gs sa grp nil :: nil) (C_True T relname)) with (Bool.true (B T)) by reflexivity.
assert (R0 : existsb (row_error O) grp = false)
  by (clear - Herr; induction grp as [ | x l IH]; [reflexivity | simpl; rewrite row_error_false; exact IH]).
cbn [slice_gs]; rewrite R0, true_is_true; cbn [orb map fst]; f_equal; [ | exact IH].
cbn [snd]; rewrite map_map; f_equal; apply map_ext; intros [e a]; reflexivity.
Qed.

Lemma full_group_rows : forall lf' items lg' c, lg' <> nil -> (forall t, er nil (slice_t T relname t :: nil) c = false) ->
  eq0 (SQ_Select (Select Set_All (S_List (map item_to items)) lf' c (G_By lg') (C_True T relname))) =
  map (fun grp => mk_row O (map (item_row (slice_gs (Fset.Union (A T) (map (sfrom_sort ORN basesort nil) lf')) grp nil :: nil)) items))
      (group_on_list O (gk lg') (filter (fun t => is_true3 T (ec nil (slice_t T relname t :: nil) c)) (PRODF lf'))).
Proof.
intros lf' items lg' c Hn Hc.
change (eq0 (SQ_Select _)) with (map (@fst _ _) (eval_sspec ORN O basesort instance nil nil
           (Select Set_All (S_List (map item_to items)) lf' c (G_By lg') (C_True T relname)) nil)).
rewrite eval_select; cbv zeta.
rewrite where_eq_g by exact Hc.
rewrite <- sr_eq_g; do 2 f_equal.
unfold grouping_part; cbv zeta; destruct lg' as [ | e lg']; [contradiction Hn; reflexivity | ].
cbn iota; f_equal; rewrite group_on_spec; unfold gkeys_of.
rewrite (map_ext_in _ (fun t => t)); [rewrite map_id; reflexivity | ].
intros t _; replace (existsb (is_error O) _) with false; [reflexivity | ].
symmetry; induction (map _ (e :: lg')) as [ | v l IH]; [reflexivity | simpl; rewrite Herr; exact IH].
Qed.


(** the labels of the rows of a [FROM] clause *)
Lemma nj_labels : forall (ss : list (Fset.set (A T))) (ll : list (list (tuple T))),
  Forall2 (fun s l => forall t, In t l -> labels T t =S= s) ss ll ->
  forall t, In t (N_join_list (tuple T) JT ET ll) -> labels T t =S= Fset.Union (A T) ss.
Proof.
intros ss ll H; induction H as [ | s l ss ll Hs H IH]; intros t It.
- destruct It as [<- | []]; rewrite Fset.Union_unfold; apply labels_empty_tuple.
- cbn [N_join_list] in It; rewrite in_brute_left_join_list in It; destruct It as [x1 [x2 [I1 [I2 ->]]]].
  rewrite Fset.Union_unfold; unfold join_tuple.
  rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)); apply Fset.union_eq; [apply Hs; exact I1 | apply IH; exact I2].
Qed.

Lemma permT_in : forall l1 l2 t, permT l1 l2 -> In t l1 -> exists t', t =t= t' /\ In t' l2.
Proof.
intros l1 l2 t P I; apply Oeset.mem_bool_true_iff; rewrite <- (Oeset.permut_mem_bool_eq t P); apply Oeset.in_mem_bool; exact I.
Qed.

Lemma permT_pointwise : forall (X : Type) (F G : X -> tuple T) l, (forall x, In x l -> F x =t= G x) -> permT (map F l) (map G l).
Proof.
intros X F G l H; induction l as [ | x l IH]; [apply Oeset.permut_refl | ].
cbn [map]; apply Oeset.permut_cons; [apply H; left; reflexivity | apply IH; intros y Iy; apply H; right; exact Iy].
Qed.

Lemma filter_true : forall (X : Type) (l : list X), filter (fun _ => true) l = l.
Proof. intros X l; induction l as [ | x l IH]; [reflexivity | simpl; f_equal; exact IH]. Qed.

Hypothesis Hcv : forall v w, canon O v = canon O w -> v = w.

(** the groups of [Sql.v] are those of [SqlFull.v], each reversed *)
Lemma key_eqb_eq : forall k1 k2, key_eqb O k1 k2 = Oset.eq_bool (mk_olists (OVal T)) k1 k2.
Proof.
intros k1 k2; unfold key_eqb.
assert (I : forall l1 l2, map (canon O) l1 = map (canon O) l2 -> l1 = l2).
{ intro l1; induction l1 as [ | x l1 IH]; intros [ | y l2] E; try discriminate E; [reflexivity | ].
  injection E; intros E2 E1; rewrite (Hcv _ _ E1), (IH _ E2); reflexivity. }
destruct (Oset.eq_bool (mk_olists (OVal T)) k1 k2) eqn:E2.
- apply Oset.eq_bool_true_iff in E2; subst; apply Oset.eq_bool_true_iff; reflexivity.
- destruct (Oset.eq_bool _ (map (canon O) k1) (map (canon O) k2)) eqn:E1; [ | reflexivity].
  apply Oset.eq_bool_true_iff, I in E1; subst; rewrite Oset.eq_bool_refl in E2; discriminate E2.
Qed.

Definition RV {X : Type} (p : list (value T) * list X) := (fst p, rev (snd p)).

Lemma ins_group : forall (x : tuple T) k acc,
  insert_in_partition (mk_olists (OVal T)) k x (map RV acc) = map RV (group_insert O k x acc).
Proof.
intros x k acc; induction acc as [ | [k' g] acc IH]; [reflexivity | ].
cbn [map insert_in_partition group_insert RV fst snd]; rewrite key_eqb_eq.
destruct (Oset.eq_bool _ k k'); cbn [map RV fst snd]; [unfold RV; cbn [fst snd]; rewrite rev_app_distr; reflexivity | rewrite IH; reflexivity].
Qed.

Lemma partition_groups : forall (key : tuple T -> list (value T)) l,
  map snd (partition (A := tuple T) (mk_olists (OVal T)) key l) = map (@rev _) (group_on_list O key l).
Proof.
intros key l; unfold partition, group_on_list.
change (@nil (list (value T) * list (tuple T))) with (map (@RV (tuple T)) nil) at 1.
generalize (@nil (list (value T) * list (tuple T))); induction l as [ | x l IH]; intro acc.
- simpl; rewrite !map_map; apply map_ext; reflexivity.
- cbn [partition_rec fold_left]; rewrite ins_group; apply IH.
Qed.

Theorem select_agree_grp : forall unknown cn lf lf' items g lg' f c,
  (forall t1 t2, t1 =t= t2 -> cn t1 = cn t2) -> well_sorted_sql_table T basesort instance ->
  Forall2 (fun it it' => permT (ef0 it') (Febag.elements BTupleT (eval_sql_from_item basesort instance unknown cn nil it))) lf lf' ->
  f_to f = Some c -> lopt at_to g = Some lg' -> lg' <> nil ->
  forallb (fun x => match x with Select_As _ e _ =>
             gcheck (Fset.Union (A T) (map (sql_from_item_sort basesort) lf)) (extract_funterms T g) e end) items = true ->
  Febag.equal BTupleT
    (Febag.mk_bag BTupleT (eq0 (SQ_Select (Select Set_All (S_List (map item_to items)) lf' c (G_By lg') (C_True T relname)))))
    (eval_sql_query basesort instance unknown cn nil
       (Sql_Select (Select_List T (_Select_List T items)) lf f (Group_By T g) (Sql_True T (sql_query T relname)))) = true.
Proof.
intros unknown cn lf lf' items g lg' f c Hcn W Hq Hf Hg Hn Hc.
set (S := Fset.Union (A T) (map (sql_from_item_sort basesort) lf)) in Hc.
rewrite full_group_rows by (exact Hn || (intro t; exact (proj2 (f_agree unknown cn (eval_sql_query basesort instance unknown cn) nil t f c Hf)))).
set (R := filter (fun t => is_true3 T (ec nil (slice_t T relname t :: nil) c)) (PRODF lf')).
set (key := fun t => map (fun x => interp_aggterm T (env_t T nil t) x) g).
assert (Kk : forall t, map (ev nil (slice_t T relname t :: nil)) lg' = key t) by (intro t; exact (lopt_at_to nil t g lg' Hg)).
rewrite (group_on_list_ext T O _ _ key) by exact Kk.
(* the labels of the rows *)
assert (HQ : Forall2 permT (map ef0 lf') (map (Febag.elements BTupleT) (map (eval_sql_from_item basesort instance unknown cn nil) lf))).
{ clear - Hq; induction Hq as [ | it it' lf lf' Hit Hq IH]; [constructor | constructor; [exact Hit | exact IH]]. }
assert (LR : forall t, In t R -> labels T t =S= S).
{ intros t It; unfold R in It; apply filter_In in It; destruct It as [It _].
  destruct (permT_in _ _ t (Oeset.permut_trans (prod_permut _) (N_join_permut _ _ HQ)) It) as [t' [Et It']].
  rewrite tuple_eq in Et; rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 Et)).
  refine (nj_labels (map (sql_from_item_sort basesort) lf) _ _ t' It').
  clear - W Hcn; induction lf as [ | it lf IH]; [constructor | constructor; [ | exact IH]].
  intros t I; apply (@well_sorted_sql_from_item T relname basesort instance unknown cn Hcn W it t nil).
  apply Febag.in_elements_mem; exact I. }
rewrite eval_sql_query_unfold; cbv beta zeta.
cbn [eval_sql_formula]; rewrite Bool.true_is_true_alt, filter_true.
rewrite Febag.nb_occ_equal; intro u; rewrite !Febag.nb_occ_mk_bag; apply Oeset.permut_nb_occ.
set (Pg := fun k => projection T (env_g T nil (Group_By T g) k) (Select_List T (_Select_List T items))).
match goal with |- permT _ (map _ (make_groups T nil ?E0 _)) => set (E := E0) end.
apply Oeset.permut_trans with (map Pg (make_groups T nil R (Group_By T g))).
- unfold make_groups; fold key; rewrite partition_groups, map_map.
  apply permT_pointwise; intros grp Ig.
  assert (Ik : In (rev grp) (map snd (partition (A := tuple T) (mk_olists (OVal T)) key R)))
    by (rewrite partition_groups; apply in_map; exact Ig).
  set (k := rev grp) in Ik |- *.
  assert (Kne := in_map_snd_partition_diff_nil _ _ _ Ik).
  assert (Kin : forall a, In a k -> In a R) by (intros a Ia; eapply in_map_snd_partition; [exact Ik | exact Ia]).
  assert (Khom : forall a b, In a k -> In b k -> key a = key b).
  { rewrite in_map_iff in Ik; destruct Ik as [[v k'] [Ek Ik]]; simpl in Ek; subst k'.
    intros a b Ia Ib; transitivity v; [ | symmetry]; eapply partition_homogeneous_values; eassumption. }
  assert (Eg : grp = rev k) by (unfold k; rewrite rev_involutive; reflexivity).
  destruct grp as [ | t1 rest]; [destruct Kne; unfold k; reflexivity | ].
  destruct (quicksort (OTuple T) k) as [ | t0 r] eqn:Hq0.
  { destruct k as [ | x k']; [destruct Kne; reflexivity | ].
    generalize (length_quicksort (OTuple T) (x :: k')); rewrite Hq0; discriminate. }
  unfold Pg, env_g; rewrite Hq0; cbn [slice_gs].
  apply row_agree_gen; intros e b Ieb; symmetry.
  apply (at_agree_g S g k t0 r t1 rest Hq0 (eq_sym Eg)).
  + intros t It; apply LR, Kin, It.
  + intros t v It Iv; exact (Khom t v It Iv).
  + rewrite forallb_forall in Hc; exact (Hc _ Ieb).
- apply (_permut_map (R := fun x y => Oeset.compare (OLTuple T) x y = Eq)).
  + intros a b _ _ H; apply projection_eq, env_g_eq_2; apply (proj2 (compare_list_t _ _ _)); exact H.
  + apply Oeset.nb_occ_permut; intro x; apply make_groups_eq; [apply equiv_env_refl | ].
    unfold E, R.
    set (Wp := fun t => Bool.is_true (B T) (eval_sql_formula unknown cn (eval_sql_query basesort instance unknown cn) (env_t T nil t) f)).
    assert (Wc : forall x y, x =t= y -> Wp x = Wp y) by (intros x1 y1 E1; unfold Wp; rewrite (f_compat unknown cn _ f c x1 y1 Hf E1); reflexivity).
    apply Oeset.permut_sym; eapply Oeset.permut_trans; [apply elements_filter_permut; exact Wc | ].
    apply Oeset.permut_sym, permut_filter_compat.
    * unfold N_join_bag; eapply Oeset.permut_trans; [ | apply Oeset.permut_sym, elements_mk_bag_permut].
      eapply Oeset.permut_trans; [apply prod_permut | apply N_join_permut; exact HQ].
    * intros x1 y1 E1; rewrite (proj1 (f_agree unknown cn (eval_sql_query basesort instance unknown cn) nil x1 f c Hf)).
      fold (Wp x1); apply Wc; exact E1.
Qed.


(** * Queries made of tables, set operations and such selections *)

Fixpoint to_full2 (q : sql_query T relname) : option (squery T relname) :=
  match q with
  | Sql_Table _ r => Some (SQ_Table T r)
  | Sql_Set o q1 q2 =>
    match to_full2 q1, to_full2 q2 with Some a, Some b => Some (SQ_Set o Set_All a b) | _, _ => None end
  | Sql_Select s lf f (Group_Fine _) (Sql_True _ _) =>
    match (fix go (lf : list (sql_from_item T relname)) : option (list (sfrom T relname)) :=
             match lf with
             | nil => Some nil
             | From_Item q1 r :: rest =>
               match to_full2 q1, go rest with Some a, Some r' => Some (Fr_Query a (ren_to r) :: r') | _, _ => None end
             end) lf, s_to s, f_to f with
    | Some lf', Some s', Some c =>
      Some (SQ_Select (Select Set_All s' lf' c (G_Fine T relname) (C_True T relname)))
    | _, _, _ => None
    end
  | Sql_Select s lf f (Group_By _ g) (Sql_True _ _) =>
    match s with
    | Select_Star _ => None
    | Select_List _ (_Select_List _ items) =>
    match (fix go (lf : list (sql_from_item T relname)) : option (list (sfrom T relname)) :=
             match lf with
             | nil => Some nil
             | From_Item q1 r :: rest =>
               match to_full2 q1, go rest with Some a, Some r' => Some (Fr_Query a (ren_to r) :: r') | _, _ => None end
             end) lf, f_to f, lopt at_to g with
    | Some lf', Some c, Some (e :: lg') =>
      if forallb (fun x => match x with Select_As _ e _ =>
                    gcheck (Fset.Union (A T) (map (sql_from_item_sort basesort) lf)) (extract_funterms T g) e end) items
      then Some (SQ_Select (Select Set_All (S_List (map item_to items)) lf' c (G_By (e :: lg')) (C_True T relname)))
      else None
    | _, _, _ => None
    end
    end
  | _ => None
  end.

Fixpoint well_sorted2 (q : sql_query T relname) : bool :=
  match q with
  | Sql_Table _ _ => true
  | Sql_Set _ q1 q2 =>
    Fset.equal (A T) (sql_sort basesort q1) (sql_sort basesort q2) && well_sorted2 q1 && well_sorted2 q2
  | Sql_Select _ lf _ _ _ =>
    (fix go (lf : list (sql_from_item T relname)) : bool :=
       match lf with nil => true | From_Item q1 _ :: r => well_sorted2 q1 && go r end) lf
  end.

Lemma lopt_sort : forall (l : list (select T)) l',
  lopt (fun x => match x with Select_As _ e a => option_map (fun e' => S_As e' a) (at_to e) end) l = Some l' ->
  map (@sitem_att T relname) l' = map (@snd _ _) (map (@select_as_as_pair T) l).
Proof.
intro l; induction l as [ | [e b] l IH]; intros l' H; simpl in H; [injection H; intros <-; reflexivity | ].
destruct e as [ft | ag ft | g la]; simpl in H; try discriminate H.
destruct (lopt _ l) as [l2 | ]; [ | discriminate H]; injection H; intros <-; simpl; f_equal; exact (IH l2 eq_refl).
Qed.

Lemma to_full2_sort : forall q q', to_full2 q = Some q' -> squery_sort ORN basesort nil q' = sql_sort basesort q.
Proof.
fix IH 1; intros q q' H; destruct q as [r | o q1 q2 | s lf f g h]; simpl in H.
- injection H; intros <-; reflexivity.
- destruct (to_full2 q1) as [a | ] eqn:E1; [ | discriminate H]; destruct (to_full2 q2) as [b | ]; [ | discriminate H].
  injection H; intros <-; exact (IH q1 a E1).
- destruct g as [g | ]; destruct h; try discriminate H.
  { destruct s as [ | [items]]; [discriminate H | ].
    match type of H with (match ?G with _ => _ end) = _ => destruct G as [qs' | ] eqn:Eg end; [ | discriminate H].
    destruct (f_to f) as [c | ]; [ | discriminate H].
    destruct (lopt at_to g) as [[ | e lg'] | ]; try discriminate H.
    destruct (forallb _ items); [ | discriminate H]; injection H; intros <-; clear H.
    cbn [squery_sort sspec_sort sql_sort]; rewrite !map_map; f_equal; apply map_ext; intros [x a]; reflexivity. }
  match type of H with (match ?G with _ => _ end) = _ => destruct G as [qs' | ] eqn:Eg end; [ | discriminate H].
  destruct (s_to s) as [s' | ] eqn:Es; [ | discriminate H].
  destruct (f_to f) as [c | ]; [ | discriminate H]; injection H; intros <-; clear H.
  destruct s as [ | [l]]; simpl in Es.
  + injection Es; intros <-; cbn [squery_sort sspec_sort sql_sort].
    fold (@sfrom_sort T relname ORN basesort) (sql_from_item_sort basesort); f_equal.
    revert qs' Eg; induction lf as [ | [q1 r] lf IHl]; intros qs' Eg; cbv beta iota fix in Eg.
    * injection Eg; intros <-; reflexivity.
    * destruct (to_full2 q1) as [a | ] eqn:E1; [ | discriminate Eg].
      match type of Eg with (match ?G with _ => _ end) = _ => destruct G as [r' | ] eqn:Er end; [ | discriminate Eg].
      injection Eg; intros <-; cbn [map]; f_equal; [ | exact (IHl r' eq_refl)].
      destruct r as [ | la]; cbn [ren_to sfrom_sort sql_from_item_sort].
      -- fold (@squery_sort T relname ORN basesort); exact (IH q1 a E1).
      -- rewrite !map_map; f_equal; apply map_ext; intros [b c]; reflexivity.
  + destruct (lopt _ l) as [l' | ] eqn:El; [ | discriminate Es]; injection Es; intros <-.
    cbn [squery_sort sspec_sort sql_sort]; rewrite (lopt_sort l l' El); reflexivity.
Qed.

Section Agree.

Hypothesis Hcanon :
  forall t u, Oeset.eq_bool (OTuple T) (canon_tuple O t) (canon_tuple O u) = Oeset.eq_bool (OTuple T) t u.
Hypothesis Hu : forall atts rows, unify_rows O atts rows = rows.

Theorem sql_full_agree2 : forall unknown cn, (forall t1 t2, t1 =t= t2 -> cn t1 = cn t2) ->
  well_sorted_sql_table T basesort instance ->
  forall q q', to_full2 q = Some q' -> well_sorted2 q = true ->
  Febag.equal BTupleT (Febag.mk_bag BTupleT (eq0 q')) (eval_sql_query basesort instance unknown cn nil q) = true.
Proof.
intros unknown cn Hcn WT; fix IH 1; intros q q' H W; destruct q as [r | o q1 q2 | s lf f g h]; simpl in H.
- injection H; intros <-; simpl; apply Febag.elements_mk_bag.
- destruct (to_full2 q1) as [a | ] eqn:Ha; [ | discriminate H]; destruct (to_full2 q2) as [b | ] eqn:Hb; [ | discriminate H].
  injection H; intros <-.
  simpl in W; rewrite !andb_true_iff in W; destruct W as [[S12 W1] W2].
  assert (S' : Fset.equal (A T) (squery_sort ORN basesort nil a) (squery_sort ORN basesort nil b) = true)
    by (rewrite (to_full2_sort _ _ Ha), (to_full2_sort _ _ Hb); exact S12).
  change (Febag.equal BTupleT (Febag.mk_bag BTupleT
            (if Fset.equal (A T) (squery_sort ORN basesort nil a) (squery_sort ORN basesort nil b)
             then unify_rows O ({{{squery_sort ORN basesort nil a}}})
                    (keep_errors O (eval_set_op O o Set_All (eq0 a) (eq0 b)) (eq0 a ++ eq0 b))
             else nil))
            (eval_sql_query basesort instance unknown cn nil (Sql_Set o q1 q2)) = true).
  rewrite S', Hu, keep_errors_id.
  set (R := eval_set_op O o Set_All (eq0 a) (eq0 b)).
  rewrite eval_sql_query_unfold, S12; simpl.
  rewrite Febag.nb_occ_equal; intro t.
  assert (K1 := IH q1 a Ha W1); assert (K2 := IH q2 b Hb W2).
  rewrite Febag.nb_occ_equal in K1, K2.
  unfold R; rewrite Febag.nb_occ_mk_bag, <- (tuple_count_nb_occ T O Hcanon t (eval_set_op O o Set_All _ _)),
    (eval_set_op_all_count T O Hcanon).
  unfold Febag.interp_set_op; destruct o;
    rewrite ?Febag.nb_occ_union_max, ?Febag.nb_occ_union, ?Febag.nb_occ_inter, ?Febag.nb_occ_diff;
    rewrite <- (K1 t), <- (K2 t), !Febag.nb_occ_mk_bag; reflexivity.
- destruct g as [g | ]; destruct h; try discriminate H.
  { destruct s as [ | [items]]; [discriminate H | ].
    match type of H with (match ?G with _ => _ end) = _ => destruct G as [qs' | ] eqn:Eg end; [ | discriminate H].
    destruct (f_to f) as [c | ] eqn:Ef; [ | discriminate H].
    destruct (lopt at_to g) as [[ | e lg'] | ] eqn:Eg'; try discriminate H.
    destruct (forallb _ items) eqn:Ec; [ | discriminate H]; injection H; intros <-; clear H.
    assert (K : Forall2 (fun it it' => permT (ef0 it') (Febag.elements BTupleT
                                       (eval_sql_from_item basesort instance unknown cn nil it))) lf qs').
    { clear Ec; simpl in W; revert qs' Eg W; induction lf as [ | [q1 r] lf IHl]; intros qs' Eg W; cbv beta iota fix in Eg.
      - injection Eg; intros <-; constructor.
      - destruct (to_full2 q1) as [a | ] eqn:E1; [ | discriminate Eg].
        match type of Eg with (match ?G with _ => _ end) = _ => destruct G as [r' | ] eqn:Er end; [ | discriminate Eg].
        injection Eg; intros <-; apply andb_true_iff in W; destruct W as [W1 W2].
        constructor; [ | exact (IHl r' eq_refl W2)].
        destruct r as [ | la]; [apply item_star | apply item_ren]; exact (IH q1 a E1 W1). }
    apply select_agree_grp; try assumption; discriminate. }
  match type of H with (match ?G with _ => _ end) = _ => destruct G as [qs' | ] eqn:Eg end; [ | discriminate H].
  destruct (s_to s) as [s' | ] eqn:Es; [ | discriminate H].
  destruct (f_to f) as [c | ] eqn:Ef; [ | discriminate H]; injection H; intros <-; clear H.
  assert (K : Forall2 (fun it it' => permT (ef0 it') (Febag.elements BTupleT
                                     (eval_sql_from_item basesort instance unknown cn nil it))) lf qs').
  { simpl in W; revert qs' Eg W; induction lf as [ | [q1 r] lf IHl]; intros qs' Eg W; cbv beta iota fix in Eg.
    - injection Eg; intros <-; constructor.
    - destruct (to_full2 q1) as [a | ] eqn:E1; [ | discriminate Eg].
      match type of Eg with (match ?G with _ => _ end) = _ => destruct G as [r' | ] eqn:Er end; [ | discriminate Eg].
      injection Eg; intros <-; apply andb_true_iff in W; destruct W as [W1 W2].
      constructor; [ | exact (IHl r' eq_refl W2)].
      destruct r as [ | la]; [apply item_star | apply item_ren]; exact (IH q1 a E1 W1). }
  apply select_agree_g; assumption.
Qed.

End Agree.

End Sec.
