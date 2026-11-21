(** * The selections of [Sql.v] and of [SqlFull.v] agree (TODO 6.1)

    The blocks [SELECT s FROM q WHERE f] of [Sql.v] without grouping, whose [SELECT] list and [WHERE] formula are
    built from function terms and predicates, translate to [SqlFull.v] ([ft_to], [f_to], [s_to]); the two
    semantics give the same bag of rows when the [FROM] query does ([select_agree]). The dialect of [SqlFull.v] is
    the one of the instance: its functions, predicates and literals are those of [T] ([Hfun], [Hpred],
    [Hconst]), it converts nothing before a comparison ([Hcoerce]), no value is a failure ([Herr], [Hpe]: [Sql.v]
    has no errors), and a NULL has no type ([Hnull]: [SqlFull.v] stores a NULL with the type of its column,
    [Sql.v] keeps the value). *)
Require Import List Bool NArith.
Require Import BasicFacts ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection ListPermut ListSort Join Projection
        FlatData Bool3 Formula Sql SqlFull SqlRelate.

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

(** * Queries made of tables, set operations and such selections *)

Fixpoint to_full2 (q : sql_query T relname) : option (squery T relname) :=
  match q with
  | Sql_Table _ r => Some (SQ_Table T r)
  | Sql_Set o q1 q2 =>
    match to_full2 q1, to_full2 q2 with Some a, Some b => Some (SQ_Set o Set_All a b) | _, _ => None end
  | Sql_Select s (From_Item q1 (Att_Ren_Star _) :: nil) f (Group_Fine _) (Sql_True _ _) =>
    match to_full2 q1, s_to s, f_to f with
    | Some a, Some s', Some c => Some (SQ_Select (Select Set_All s' (Fr_Query a (Ren_Star T) :: nil) c (G_Fine T relname) (C_True T relname)))
    | _, _, _ => None
    end
  | _ => None
  end.

Fixpoint well_sorted2 (q : sql_query T relname) : bool :=
  match q with
  | Sql_Table _ _ => true
  | Sql_Set _ q1 q2 =>
    Fset.equal (A T) (sql_sort basesort q1) (sql_sort basesort q2) && well_sorted2 q1 && well_sorted2 q2
  | Sql_Select _ (From_Item q1 _ :: nil) _ _ _ => well_sorted2 q1
  | _ => true
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
- destruct lf as [ | [q1 [ | la]] [ | x lf]]; try discriminate H; destruct g; try discriminate H;
    destruct h; try discriminate H.
  destruct (to_full2 q1) as [a | ] eqn:E1; [ | discriminate H]; destruct (s_to s) as [s' | ] eqn:Es; [ | discriminate H].
  destruct (f_to f) as [c | ]; [ | discriminate H]; injection H; intros <-.
  destruct s as [ | [l]]; simpl in Es.
  + injection Es; intros <-; cbn [squery_sort sspec_sort sfrom_sort sql_sort sql_from_item_sort map].
    fold (@squery_sort T relname ORN basesort) (sql_sort basesort); rewrite (IH q1 a E1); reflexivity.
  + destruct (lopt _ l) as [l' | ] eqn:El; [ | discriminate Es]; injection Es; intros <-.
    cbn [squery_sort sspec_sort sql_sort]; rewrite (lopt_sort l l' El); reflexivity.
Qed.

Section Agree.

Hypothesis Hcanon :
  forall t u, Oeset.eq_bool (OTuple T) (canon_tuple O t) (canon_tuple O u) = Oeset.eq_bool (OTuple T) t u.
Hypothesis Hu : forall atts rows, unify_rows O atts rows = rows.

Theorem sql_full_agree2 : forall unknown cn q q', to_full2 q = Some q' -> well_sorted2 q = true ->
  Febag.equal BTupleT (Febag.mk_bag BTupleT (eq0 q')) (eval_sql_query basesort instance unknown cn nil q) = true.
Proof.
intros unknown cn; fix IH 1; intros q q' H W; destruct q as [r | o q1 q2 | s lf f g h]; simpl in H.
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
- destruct lf as [ | [q1 [ | la]] [ | x lf]]; try discriminate H; destruct g; try discriminate H;
    destruct h; try discriminate H.
  destruct (to_full2 q1) as [a | ] eqn:E1; [ | discriminate H]; destruct (s_to s) as [s' | ] eqn:Es; [ | discriminate H].
  destruct (f_to f) as [c | ] eqn:Ef; [ | discriminate H]; injection H; intros <-.
  simpl in W; apply select_agree; [exact (IH q1 a E1 W) | exact Es | exact Ef].
Qed.

End Agree.

End Sec.
