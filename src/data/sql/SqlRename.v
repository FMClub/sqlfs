(** * Renaming the attributes (TODO 6.3, issue I4)

    The evaluation of [SqlFull.v] does not depend on the names of the attributes: for a bijection [rho] of
    the attributes which preserves their order, their types and their affinities, and fixes the attribute of
    the failed rows, the rows of the renamed query over the renamed database are the renamed rows of the query
    ([eval_rename]). The front end names the columns of each item of a [FROM] clause and of each derived table
    by their positions, so that the named semantics of [SqlFull.v] is a positional semantics in which two
    columns never share a name; this theorem says that the choice of the names does not matter. *)
Require Import List Bool Sorting.
Require Import BasicFacts ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection FlatData SqlFull SqlInduction.
Import Tuple.

Section Sec.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.
Hypothesis ORN : Oset.Rcd relname.
Hypothesis rho : attribute T -> attribute T.
Hypothesis rhoi : attribute T -> attribute T.
Hypothesis Hrr : forall a, rhoi (rho a) = a.
Hypothesis Hrr' : forall b, rho (rhoi b) = b.
Hypothesis Hord : forall a b, Oset.compare (OAtt T) (rho a) (rho b) = Oset.compare (OAtt T) a b.
Hypothesis Hty : forall a, type_of_attribute T (rho a) = type_of_attribute T a.

Lemma rho_inj : forall a b, rho a = rho b -> a = b.
Proof. intros a b H; rewrite <- (Hrr a), <- (Hrr b), H; reflexivity. Qed.

Lemma rho_eqb : forall a b, Oset.eq_bool (OAtt T) (rho a) (rho b) = Oset.eq_bool (OAtt T) a b.
Proof. intros a b; unfold Oset.eq_bool; rewrite Hord; reflexivity. Qed.

(** the renamed sets *)
Definition rs (s : Fset.set (A T)) := Fset.mk_set (A T) (map rho ({{{s}}})).

Lemma mem_rs : forall s a, (rho a inS? rs s) = (a inS? s).
Proof.
intros s a; unfold rs; rewrite Fset.mem_mk_set, Fset.mem_elements.
induction ({{{s}}}) as [ | x l IH]; [reflexivity | ].
simpl; rewrite rho_eqb, IH; unfold Oset.eq_bool; reflexivity.
Qed.

Lemma mem_rs' : forall s b, (b inS? rs s) = (rhoi b inS? s).
Proof. intros s b; rewrite <- (Hrr' b) at 1; rewrite mem_rs; reflexivity. Qed.

Lemma rs_eq : forall s1 s2, s1 =S= s2 -> rs s1 =S= rs s2.
Proof. intros s1 s2 H; rewrite Fset.equal_spec; intro b; rewrite !mem_rs'; apply Fset.mem_eq_2; exact H. Qed.

Lemma rs_union : forall s1 s2, rs (s1 unionS s2) =S= (rs s1 unionS rs s2).
Proof. intros s1 s2; rewrite Fset.equal_spec; intro b; rewrite Fset.mem_union, !mem_rs', Fset.mem_union; reflexivity. Qed.

Lemma rs_singleton : forall a, rs (Fset.singleton (A T) a) =S= Fset.singleton (A T) (rho a).
Proof.
intro a; rewrite Fset.equal_spec; intro b; rewrite mem_rs', !Fset.singleton_spec.
rewrite <- (Hrr' b) at 2; rewrite rho_eqb; reflexivity.
Qed.

Lemma rs_mk_set : forall l, rs (Fset.mk_set (A T) l) =S= Fset.mk_set (A T) (map rho l).
Proof.
intro l; rewrite Fset.equal_spec; intro b; rewrite mem_rs', !Fset.mem_mk_set.
rewrite <- (Hrr' b) at 2; induction l as [ | x l IH]; [reflexivity | simpl; rewrite rho_eqb, IH; reflexivity].
Qed.

Lemma rs_empty : rs (Fset.empty (A T)) =S= Fset.empty (A T).
Proof. rewrite Fset.equal_spec; intro b; rewrite mem_rs', !Fset.empty_spec; reflexivity. Qed.

(** the elements of a renamed set, in order *)
Lemma sorted_map_rho : forall l, Sorted (fun x y => Oset.compare (OAtt T) x y = Lt) l ->
  Sorted (fun x y => Oset.compare (OAtt T) x y = Lt) (map rho l).
Proof.
intros l H; induction H as [ | x l H IH Hx]; simpl; constructor; [exact IH | ].
destruct Hx as [ | y l Hy]; constructor; rewrite Hord; exact Hy.
Qed.

Lemma sorted_same : forall l1 l2,
  Sorted (fun x y => Oset.compare (OAtt T) x y = Lt) l1 -> Sorted (fun x y => Oset.compare (OAtt T) x y = Lt) l2 ->
  (forall x, In x l1 <-> In x l2) -> l1 = l2.
Proof.
assert (Tr : Relations_1.Transitive (fun x y : attribute T => Oset.compare (OAtt T) x y = Lt))
  by (intros x y z; apply Oset.compare_lt_trans).
intros l1 l2 S1 S2; apply Sorted_StronglySorted in S1; [ | exact Tr]; apply Sorted_StronglySorted in S2; [ | exact Tr].
revert l2 S2; induction S1 as [ | x l1 S1 IH F1]; intros l2 S2 H.
- destruct l2 as [ | y l2]; [reflexivity | destruct (proj2 (H y) (or_introl eq_refl))].
- destruct S2 as [ | y l2 S2 F2]; [destruct (proj1 (H x) (or_introl eq_refl)) | ].
  assert (Exy : x = y).
  { destruct (proj1 (H x) (or_introl eq_refl)) as [E | I]; [exact (eq_sym E) | ].
    destruct (proj2 (H y) (or_introl eq_refl)) as [E | J]; [exact E | ].
    rewrite Forall_forall in F1, F2; generalize (F1 y J) (F2 x I); intros A1 A2.
    rewrite Oset.compare_lt_gt, A2 in A1; discriminate A1. }
  subst y; f_equal; apply IH; [exact S2 | ].
  intro z; split; intro Iz.
  + destruct (proj1 (H z) (or_intror Iz)) as [E | J]; [ | exact J].
    subst z; rewrite Forall_forall in F1; generalize (F1 x Iz); rewrite Oset.compare_eq_refl; discriminate.
  + destruct (proj2 (H z) (or_intror Iz)) as [E | J]; [ | exact J].
    subst z; rewrite Forall_forall in F2; generalize (F2 x Iz); rewrite Oset.compare_eq_refl; discriminate.
Qed.

Lemma in_elements_iff : forall (s : Fset.set (A T)) (x : attribute T), In x ({{{s}}}) <-> x inS s.
Proof.
intros s x; split; intro H; [apply Fset.in_elements_mem; exact H | apply Fset.mem_in_elements; exact H].
Qed.

Lemma elements_rs : forall s, {{{rs s}}} = map rho ({{{s}}}).
Proof.
intro s; apply sorted_same.
- apply Fset.elements_spec3.
- apply sorted_map_rho; apply Fset.elements_spec3.
- intro x; rewrite in_elements_iff; unfold rs; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff; tauto.
Qed.

(** the renamed tuples *)
Definition rt (t : tuple T) := mk_tuple T (rs (labels T t)) (fun b => dot T t (rhoi b)).

Lemma labels_rt : forall t, labels T (rt t) =S= rs (labels T t).
Proof. intro t; apply labels_mk_tuple. Qed.

Lemma dot_rt : forall t a, a inS labels T t -> dot T (rt t) (rho a) = dot T t a.
Proof. intros t a H; unfold rt; rewrite dot_mk_tuple, mem_rs, H, Hrr; reflexivity. Qed.

Lemma mem_rt : forall t a, (rho a inS? labels T (rt t)) = (a inS? labels T t).
Proof. intros t a; rewrite (Fset.mem_eq_2 _ _ _ (labels_rt t)); apply mem_rs. Qed.

(** two tuples related by the renaming *)
Definition RT (t' t : tuple T) := t' =t= rt t.

Lemma RT_labels : forall t' t, RT t' t -> labels T t' =S= rs (labels T t).
Proof.
intros t' t H; unfold RT in H; rewrite tuple_eq in H.
rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 H)); apply labels_rt.
Qed.

Lemma RT_mem : forall t' t a, RT t' t -> (rho a inS? labels T t') = (a inS? labels T t).
Proof. intros t' t a H; rewrite (Fset.mem_eq_2 _ _ _ (RT_labels _ _ H)); apply mem_rs. Qed.

Lemma RT_dot : forall t' t a, RT t' t -> a inS labels T t -> dot T t' (rho a) = dot T t a.
Proof.
intros t' t a H Ha; unfold RT in H; rewrite tuple_eq in H; rewrite (proj2 H).
- apply dot_rt; exact Ha.
- rewrite (Fset.mem_eq_2 _ _ _ (proj1 H)), (Fset.mem_eq_2 _ _ _ (labels_rt t)), mem_rs; exact Ha.
Qed.

(** a missing attribute of a tuple has the default value of its type *)
Hypothesis Hdot : forall t a, (a inS? labels T t) = false -> dot T t a = default_value T (type_of_attribute T a).

Lemma RT_dot_all : forall t' t a, RT t' t -> dot T t' (rho a) = dot T t a.
Proof.
intros t' t a H; destruct (a inS? labels T t) eqn:Ha; [apply RT_dot; assumption | ].
rewrite Hdot, Hdot, Hty; [reflexivity | exact Ha | rewrite (RT_mem _ _ _ H); exact Ha].
Qed.

Lemma RT_dot' : forall t' t b, RT t' t -> dot T t' b = dot T t (rhoi b).
Proof. intros t' t b H; rewrite <- (Hrr' b) at 1; apply RT_dot_all; exact H. Qed.

Lemma RT_intro : forall t' t, labels T t' =S= rs (labels T t) -> (forall a, a inS labels T t -> dot T t' (rho a) = dot T t a) ->
  RT t' t.
Proof.
intros t' t Hl Hd; unfold RT; rewrite tuple_eq; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ Hl), (Fset.equal_eq_2 _ _ _ _ (labels_rt t)); apply Fset.equal_refl.
- intros b Hb; rewrite (Fset.mem_eq_2 _ _ _ Hl), mem_rs' in Hb.
  rewrite <- (Hrr' b), Hd, dot_rt; [reflexivity | exact Hb | exact Hb].
Qed.

Lemma RT_rt : forall t, RT (rt t) t.
Proof. intro t; apply Oeset.compare_eq_refl. Qed.

Lemma RT_eq_l : forall t1' t2' t, t1' =t= t2' -> RT t2' t -> RT t1' t.
Proof. intros t1' t2' t E H; unfold RT in *; eapply Oeset.compare_eq_trans; eassumption. Qed.

Lemma RT_eq_r : forall t' t1 t2, t1 =t= t2 -> RT t' t1 -> RT t' t2.
Proof.
intros t' t1 t2 E H; apply RT_intro.
- rewrite (Fset.equal_eq_1 _ _ _ _ (RT_labels _ _ H)); apply rs_eq; rewrite tuple_eq in E; exact (proj1 E).
- intros a Ha; rewrite (RT_dot_all _ _ _ H); rewrite tuple_eq in E; apply (proj2 E).
  rewrite (Fset.mem_eq_2 _ _ _ (proj1 E)); exact Ha.
Qed.

Lemma RT_mk_tuple : forall s s' f f', s' =S= rs s -> (forall a, a inS s -> f' (rho a) = f a) ->
  RT (mk_tuple T s' f') (mk_tuple T s f).
Proof.
intros s s' f f' Hs Hf; apply RT_intro.
- rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)); rewrite (Fset.equal_eq_1 _ _ _ _ Hs).
  apply rs_eq; rewrite Fset.equal_spec; intro x; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)); reflexivity.
- intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha; rewrite !dot_mk_tuple.
  rewrite (Fset.mem_eq_2 _ _ _ Hs), mem_rs, Ha; apply Hf; exact Ha.
Qed.

Lemma RT_join : forall t1' t1 t2' t2, RT t1' t1 -> RT t2' t2 -> RT (join_tuple T t1' t2') (join_tuple T t1 t2).
Proof.
intros t1' t1 t2' t2 H1 H2; unfold join_tuple; apply RT_mk_tuple.
- rewrite Fset.equal_spec; intro b; rewrite Fset.mem_union, !mem_rs', Fset.mem_union.
  rewrite <- (Hrr' b) at 1 2; rewrite (RT_mem _ _ _ H1), (RT_mem _ _ _ H2); reflexivity.
- intros a _; rewrite (RT_mem _ _ _ H1); destruct (a inS? labels T t1); [apply RT_dot_all | apply RT_dot_all]; assumption.
Qed.

Lemma RT_empty : RT (empty_tuple T) (empty_tuple T).
Proof.
unfold empty_tuple; apply RT_mk_tuple; [ | intros; rewrite Hty; reflexivity].
rewrite Fset.equal_spec; intro b; rewrite mem_rs', !Fset.empty_spec; reflexivity.
Qed.

(** two related tuples are equal when the tuples they rename are *)
Lemma RT_compare : forall t1' t1 t2' t2, RT t1' t1 -> RT t2' t2 ->
  (Oeset.compare (OTuple T) t1' t2' = Eq <-> Oeset.compare (OTuple T) t1 t2 = Eq).
Proof.
intros t1' t1 t2' t2 H1 H2; rewrite !tuple_eq; split; intros [L D].
- split.
  + rewrite Fset.equal_spec; intro a; rewrite <- (RT_mem _ _ _ H1), <- (RT_mem _ _ _ H2); apply Fset.mem_eq_2; exact L.
  + intros a Ha; rewrite <- (RT_dot_all _ _ _ H1), <- (RT_dot_all _ _ _ H2); apply D; rewrite (RT_mem _ _ _ H1); exact Ha.
- split.
  + rewrite Fset.equal_spec; intro b; rewrite <- (Hrr' b), (RT_mem _ _ _ H1), (RT_mem _ _ _ H2); apply Fset.mem_eq_2; exact L.
  + intros b Hb; rewrite (RT_dot' _ _ _ H1), (RT_dot' _ _ _ H2); apply D.
    rewrite <- (RT_mem _ _ _ H1), Hrr'; exact Hb.
Qed.

Lemma RT_eq_bool : forall t1' t1 t2' t2, RT t1' t1 -> RT t2' t2 ->
  Oeset.eq_bool (OTuple T) t1' t2' = Oeset.eq_bool (OTuple T) t1 t2.
Proof.
intros t1' t1 t2' t2 H1 H2; generalize (RT_compare _ _ _ _ H1 H2); unfold Oeset.eq_bool.
destruct (Oeset.compare (OTuple T) t1' t2'); destruct (Oeset.compare (OTuple T) t1 t2); intros [A B];
  try reflexivity; [discriminate (A eq_refl) | discriminate (A eq_refl) | discriminate (B eq_refl) | discriminate (B eq_refl)].
Qed.

Lemma elements_labels_RT : forall t' t, RT t' t -> {{{labels T t'}}} = map rho ({{{labels T t}}}).
Proof. intros t' t H; rewrite <- elements_rs; apply (Fset.elements_spec1 _ _ _ (RT_labels _ _ H)). Qed.

(** lists of related tuples *)
Definition RL := Forall2 RT.

Lemma RL_map : forall (X Y : Type) (f : X -> tuple T) (g : Y -> tuple T) (P : X -> Y -> Prop) l1 l2,
  Forall2 P l1 l2 -> (forall x y, P x y -> RT (f x) (g y)) -> RL (map f l1) (map g l2).
Proof. intros X Y f g P l1 l2 H K; induction H; constructor; auto. Qed.

Lemma RL_app : forall l1 l2 l1' l2', RL l1 l2 -> RL l1' l2' -> RL (l1 ++ l1') (l2 ++ l2').
Proof. intros; apply Forall2_app; assumption. Qed.

(** * The renaming of the queries *)

Notation sexpr := (sexpr T relname).
Notation scond := (scond T relname).
Notation squery := (squery T relname).
Notation sspec := (sspec T relname).
Notation sfrom := (sfrom T relname).

Definition r_ren (r : SqlFull.renaming T) : SqlFull.renaming T :=
  match r with
  | Ren_List _ l => Ren_List T (map (fun x => (rho (fst x), rho (snd x))) l)
  | _ => Ren_Star T
  end.

Fixpoint r_e (e : sexpr) : sexpr :=
  match e with
  | E_Const _ _ v => E_Const T relname v
  | E_Col _ _ a => E_Col T relname (rho a)
  | E_Fun f l => E_Fun f (map r_e l)
  | E_Agg ag sq e c => E_Agg ag sq (r_e e) (r_c c)
  | E_AggX ag sq e sep lo c =>
    E_AggX ag sq (r_e e) (match sep with Some s => Some (r_e s) | None => None end)
           (map (fun o => match o with O_By e d n => O_By (r_e e) d n end) lo) (r_c c)
  | E_Case c e1 e2 => E_Case (r_c c) (r_e e1) (r_e e2)
  | E_Cond c => E_Cond (r_c c)
  | E_Sub q => E_Sub (r_q q)
  | E_Grouping x => E_Grouping (r_e x)
  end

with r_c (c : scond) : scond :=
  match c with
  | C_Conj a c1 c2 => C_Conj a (r_c c1) (r_c c2)
  | C_Not c => C_Not (r_c c)
  | C_True _ _ => C_True T relname
  | C_Pred p l => C_Pred p (map r_e l)
  | C_Expr e => C_Expr (r_e e)
  | C_Quant qtf p l q la => C_Quant qtf p (map r_e l) (r_q q) (map rho la)
  | C_In l q la => C_In (map r_e l) (r_q q) (map rho la)
  | C_Exists q => C_Exists (r_q q)
  end

with r_q (q : squery) : squery :=
  match q with
  | SQ_Table _ r => SQ_Table T r
  | SQ_Set o sq q1 q2 => SQ_Set o sq (r_q q1) (r_q q2)
  | SQ_Select sp => SQ_Select (r_s sp)
  | SQ_Order q lo off lim => SQ_Order (r_q q) (map (fun o => match o with O_By e d n => O_By (r_e e) d n end) lo) off lim
  | SQ_Fetch q lo off ties pct n =>
    SQ_Fetch (r_q q) (map (fun o => match o with O_By e d n => O_By (r_e e) d n end) lo) off ties pct n
  | SQ_Window q lw =>
    SQ_Window (r_q q)
      (map (fun w => match w with
                     | W_As f lp lo a =>
                       W_As ((fix r_w (f : swfun T relname) : swfun T relname :=
                                match f with
                                | W_Agg ag sq e fr => W_Agg ag sq (r_e e) fr
                                | W_Lag e n d => W_Lag (r_e e) n (r_e d)
                                | W_Lead e n d => W_Lead (r_e e) n (r_e d)
                                | W_First_Value e fr => W_First_Value (r_e e) fr
                                | W_Last_Value e fr => W_Last_Value (r_e e) fr
                                | W_Nth_Value e n fr => W_Nth_Value (r_e e) n fr
                                | W_Opts f' ign last => W_Opts (r_w f') ign last
                                | f => f
                                end) f)
                            (map r_e lp) (map (fun o => match o with O_By e d n => O_By (r_e e) d n end) lo) (rho a)
                     end) lw)
  | SQ_With r q1 q2 => SQ_With r (r_q q1) (r_q q2)
  | SQ_WithRec sq r q1 q2 q3 => SQ_WithRec sq r (r_q q1) (r_q q2) (r_q q3)
  end

with r_s (sp : sspec) : sspec :=
  match sp with
  | Select sq s lf w g h =>
    Select sq
      (match s with
       | S_Star _ _ => S_Star T relname
       | S_List l => S_List (map (fun it => match it with S_As e a => S_As (r_e e) (rho a) end) l)
       end)
      (map r_f lf) (r_c w)
      (match g with
       | G_Fine _ _ => G_Fine T relname
       | G_By l => G_By (map r_e l)
       | G_Sets ss => G_Sets (map (map r_e) ss)
       | G_Rollup l => G_Rollup (map r_e l)
       | G_Cube l => G_Cube (map r_e l)
       end) (r_c h)
  end

with r_f (f : sfrom) : sfrom :=
  match f with
  | Fr_Query q r => Fr_Query (r_q q) (r_ren r)
  | Fr_Join jt lat f1 f2 c => Fr_Join jt lat (r_f f1) (r_f f2) (r_c c)
  | Fr_Fun name args ord atts => Fr_Fun name (map r_e args) ord (map rho atts)
  end.

(** * Static functions of the renamed queries *)

Hypothesis basesort basesort' : relname -> Fset.set (A T).
Hypothesis Hbs : forall r, basesort' r =S= rs (basesort r).

Notation rq := r_q.
Notation rsp := r_s.
Notation rf := r_f.
Notation re := r_e.
Notation rc := r_c.
Notation sq_sort' := (squery_sort ORN basesort').
Notation sq_sort := (squery_sort ORN basesort).

Lemma rs_Union : forall l, rs (Fset.Union (A T) l) =S= Fset.Union (A T) (map rs l).
Proof.
intro l; rewrite Fset.equal_spec; intro b; rewrite mem_rs'.
induction l as [ | s l IH]; cbn [map].
- rewrite !Fset.Union_unfold, !Fset.empty_spec; reflexivity.
- rewrite (Fset.Union_unfold _ (s :: l)), (Fset.Union_unfold _ (rs s :: map rs l)), !Fset.mem_union, IH, mem_rs'; reflexivity.
Qed.

Lemma Union_eq_F2 : forall l1 l2, Forall2 (fun s1 s2 => s1 =S= s2) l1 l2 -> Fset.Union (A T) l1 =S= Fset.Union (A T) l2.
Proof.
intros l1 l2 H; induction H as [ | s1 s2 l1 l2 E H IH]; [apply Fset.equal_refl | ].
rewrite (Fset.Union_unfold _ (s1 :: l1)), (Fset.Union_unfold _ (s2 :: l2)); apply Fset.union_eq; assumption.
Qed.

(** the sorts of the [WITH] relations *)
Definition Rsort (ce' ce : SqlFull.cte_env T relname) :=
  Forall2 (fun x' x => fst x' = fst x /\ fst (snd x') =S= rs (fst (snd x))) ce' ce.

Lemma Rsort_find : forall ce' ce r, Rsort ce' ce ->
  match Oset.find ORN r ce', Oset.find ORN r ce with
  | Some (s', _), Some (s, _) => s' =S= rs s
  | None, None => True
  | _, _ => False
  end.
Proof.
intros ce' ce r H; induction H as [ | [r' [s' l']] [r0 [s l]] ce' ce [E1 E2] H IH]; [exact I | ].
simpl in E1, E2; subst r'; cbn [Oset.find Mem.find fst].
unfold Oset.find in IH; destruct (Oset.eq_bool ORN r r0); [exact E2 | exact IH].
Qed.

Lemma Rsort_cons : forall ce' ce r s' s l' l, Rsort ce' ce -> s' =S= rs s -> Rsort ((r, (s', l')) :: ce') ((r, (s, l)) :: ce).
Proof. intros; constructor; [split; [reflexivity | assumption] | assumption]. Qed.



Lemma sort_rename : forall q ce' ce, Rsort ce' ce -> sq_sort' ce' (rq q) =S= rs (sq_sort ce q)
with sort_rename_s : forall sp ce' ce, Rsort ce' ce -> sspec_sort ORN basesort' ce' (rsp sp) =S= rs (sspec_sort ORN basesort ce sp)
with sort_rename_f : forall f ce' ce, Rsort ce' ce -> sfrom_sort ORN basesort' ce' (rf f) =S= rs (sfrom_sort ORN basesort ce f).
Proof.
- intros [r | o sq q1 q2 | sp | q lo off lim | q lo off ties pct n | q lw | r q1 q2 | sq r q1 q2 q3] ce' ce H; cbn [r_q squery_sort].
  + generalize (Rsort_find _ _ r H); destruct (Oset.find ORN r ce') as [[s' l'] | ]; destruct (Oset.find ORN r ce) as [[s l] | ];
      intro K; try contradiction K; [exact K | apply Hbs].
  + apply sort_rename; exact H.
  + apply sort_rename_s; exact H.
  + apply sort_rename; exact H.
  + apply sort_rename; exact H.
  + rewrite (Fset.equal_eq_2 _ _ _ _ (rs_union _ _)); apply Fset.union_eq; [apply sort_rename; exact H | ].
    rewrite (Fset.equal_eq_2 _ _ _ _ (rs_mk_set _)), map_map, map_map.
    apply Fset.equal_refl_alt; f_equal; apply map_ext; intros [f lp lo a]; reflexivity.
  + apply sort_rename; apply Rsort_cons; [exact H | apply sort_rename; exact H].
  + apply sort_rename; apply Rsort_cons; [exact H | apply sort_rename; exact H].
- intros [sq s lf w g h] ce' ce H; destruct s as [ | l]; cbn [r_s sspec_sort].
  + rewrite (Fset.equal_eq_2 _ _ _ _ (rs_Union _)), map_map, map_map; apply Union_eq_F2.
    induction lf as [ | f lf IH]; constructor; [apply sort_rename_f; exact H | exact IH].
  + rewrite (Fset.equal_eq_2 _ _ _ _ (rs_mk_set _)), !map_map.
    apply Fset.equal_refl_alt; f_equal; apply map_ext; intros [e a]; reflexivity.
- intros [q r | jt lat f1 f2 c | name args ord atts] ce' ce H; cbn [r_f sfrom_sort].
  + destruct r as [ | l]; cbn [r_ren sfrom_sort]; [apply sort_rename; exact H | ].
    rewrite (Fset.equal_eq_2 _ _ _ _ (rs_mk_set _)), !map_map; apply Fset.equal_refl.
  + rewrite (Fset.equal_eq_2 _ _ _ _ (rs_union _ _)); apply Fset.union_eq; apply sort_rename_f; exact H.
  + rewrite (Fset.equal_eq_2 _ _ _ _ (rs_mk_set _)); apply Fset.equal_refl.
Qed.

Lemma eqb_rename : forall x y : SqlFull.sexpr T relname, sexpr_eqb (re x) (re y) = sexpr_eqb x y.
Proof.
fix IH 1; intros [v | a | f l | ag sq e c | ag sq e sep lo c | c e1 e2 | c | q | x'] y;
  destruct y as [v' | a' | f' l' | ag' sq' e' c' | ag' sq' e' sep' lo' c' | c' e1' e2' | c' | q' | y']; try reflexivity.
- cbn [r_e sexpr_eqb]; apply rho_eqb.
- cbn [r_e sexpr_eqb]; f_equal.
  revert l'; induction l as [ | x l IHl]; intros [ | y l']; try reflexivity.
  cbn [map]; rewrite IH, IHl; reflexivity.
Qed.

(** the columns which are read *)
Lemma filter_map_rho : forall (p p' : attribute T -> bool) l, (forall a, p' (rho a) = p a) ->
  filter p' (map rho l) = map rho (filter p l).
Proof. intros p p' l H; induction l as [ | a l IH]; [reflexivity | simpl; rewrite H; destruct (p a); simpl; rewrite IH; reflexivity]. Qed.

Lemma flat_map_rho : forall (X : Type) (f : X -> list (attribute T)) (g : X -> list (attribute T)) (h : X -> X) l,
  (forall x, In x l -> g (h x) = map rho (f x)) -> flat_map g (map h l) = map rho (flat_map f l).
Proof.
intros X f g h l H; induction l as [ | x l IH]; [reflexivity | ].
cbn [map flat_map]; rewrite map_app, H, IH; [reflexivity | intros y Iy; apply H; right; exact Iy | left; reflexivity].
Qed.

Notation sc_e' := (sexpr_cols ORN basesort').
Notation sc_e := (sexpr_cols ORN basesort).

Ltac fold_cols ce' ce :=
  fold (sexpr_cols ORN basesort' ce') (sexpr_cols ORN basesort ce) (scond_cols ORN basesort' ce')
       (scond_cols ORN basesort ce) (squery_cols ORN basesort' ce') (squery_cols ORN basesort ce)
       (sspec_cols ORN basesort' ce') (sspec_cols ORN basesort ce) (sfrom_cols ORN basesort' ce')
       (sfrom_cols ORN basesort ce).

Definition Ce (e : SqlFull.sexpr T relname) := forall ce' ce, Rsort ce' ce -> sc_e' ce' (re e) = map rho (sc_e ce e).
Definition Cc (c : SqlFull.scond T relname) := forall ce' ce, Rsort ce' ce ->
  scond_cols ORN basesort' ce' (rc c) = map rho (scond_cols ORN basesort ce c).
Definition Cq (q : SqlFull.squery T relname) := forall ce' ce, Rsort ce' ce ->
  squery_cols ORN basesort' ce' (rq q) = map rho (squery_cols ORN basesort ce q).
Definition Cs (sp : SqlFull.sspec T relname) := forall ce' ce, Rsort ce' ce ->
  sspec_cols ORN basesort' ce' (rsp sp) = map rho (sspec_cols ORN basesort ce sp).
Definition Cf (f : SqlFull.sfrom T relname) := forall ce' ce, Rsort ce' ce ->
  sfrom_cols ORN basesort' ce' (rf f) = map rho (sfrom_cols ORN basesort ce f).

Lemma Cflat : forall l ce' ce, LE T relname Ce l -> Rsort ce' ce ->
  flat_map (sc_e' ce') (map re l) = map rho (flat_map (sc_e ce) l).
Proof. intros l ce' ce H R; apply flat_map_rho; intros x Ix; apply (H x Ix); exact R. Qed.

Lemma Cflat_o : forall (lo : list (sorder T relname)) ce' ce, LO T relname Ce lo -> Rsort ce' ce ->
  flat_map (fun o => match o with O_By e _ _ => sc_e' ce' e end)
           (map (fun o => match o with O_By e d n => O_By (re e) d n end) lo) =
  map rho (flat_map (fun o => match o with O_By e _ _ => sc_e ce e end) lo).
Proof. intros lo ce' ce H R; apply flat_map_rho; intros [x d n] Ix; apply (H x d n Ix); exact R. Qed.

Ltac kcols := intros; intros ce' ce H; cbn [r_e r_c r_q r_s r_f sexpr_cols scond_cols squery_cols sspec_cols sfrom_cols];
              fold_cols ce' ce.

Lemma k_const : forall v, Ce (E_Const T relname v). Proof. kcols; reflexivity. Qed.
Lemma k_col : forall a, Ce (E_Col T relname a). Proof. kcols; reflexivity. Qed.
Lemma k_fun : forall f l, LE T relname Ce l -> Ce (E_Fun f l). Proof. intros f l Hl; kcols; apply Cflat; assumption. Qed.
Lemma k_agg : forall ag sq e c, Ce e -> Cc c -> Ce (E_Agg ag sq e c).
Proof. intros ag sq e c He Hc; kcols; rewrite map_app, (He ce' ce H), (Hc ce' ce H); reflexivity. Qed.
Lemma k_aggx : forall ag sq e sep lo c, Ce e -> (forall s, sep = Some s -> Ce s) -> LO T relname Ce lo -> Cc c ->
  Ce (E_AggX ag sq e sep lo c).
Proof.
intros ag sq e sep lo c He Hs Hlo Hc; kcols; rewrite !map_app, (He ce' ce H), (Hc ce' ce H), (Cflat_o lo ce' ce Hlo H).
destruct sep as [x | ]; [rewrite (Hs x eq_refl ce' ce H) | ]; reflexivity.
Qed.
Lemma k_case : forall c e1 e2, Cc c -> Ce e1 -> Ce e2 -> Ce (E_Case c e1 e2).
Proof. intros c e1 e2 Hc H1 H2; kcols; rewrite !map_app, (Hc ce' ce H), (H1 ce' ce H), (H2 ce' ce H); reflexivity. Qed.
Lemma k_cond : forall c, Cc c -> Ce (E_Cond c). Proof. intros c Hc; kcols; apply Hc; exact H. Qed.
Lemma k_sub : forall q, Cq q -> Ce (E_Sub q). Proof. intros q Hq; kcols; apply Hq; exact H. Qed.
Lemma k_grouping : forall x, Ce x -> Ce (E_Grouping x). Proof. intros x Hx; kcols; apply Hx; exact H. Qed.
Lemma k_conj : forall a c1 c2, Cc c1 -> Cc c2 -> Cc (C_Conj a c1 c2).
Proof. intros a c1 c2 H1 H2; kcols; rewrite map_app, (H1 ce' ce H), (H2 ce' ce H); reflexivity. Qed.
Lemma k_not : forall c, Cc c -> Cc (C_Not c). Proof. intros c Hc; kcols; apply Hc; exact H. Qed.
Lemma k_true : Cc (C_True T relname). Proof. kcols; reflexivity. Qed.
Lemma k_pred : forall p l, LE T relname Ce l -> Cc (C_Pred p l). Proof. intros p l Hl; kcols; apply Cflat; assumption. Qed.
Lemma k_expr : forall e, Ce e -> Cc (C_Expr e). Proof. intros e He; kcols; apply He; exact H. Qed.
Lemma k_quant : forall qtf p l q la, LE T relname Ce l -> Cq q -> Cc (C_Quant qtf p l q la).
Proof. intros qtf p l q la Hl Hq; kcols; rewrite map_app, (Hq ce' ce H), (Cflat l ce' ce Hl H); reflexivity. Qed.
Lemma k_in : forall l q la, LE T relname Ce l -> Cq q -> Cc (C_In l q la).
Proof. intros l q la Hl Hq; kcols; rewrite map_app, (Hq ce' ce H), (Cflat l ce' ce Hl H); reflexivity. Qed.
Lemma k_exists : forall q, Cq q -> Cc (C_Exists q). Proof. intros q Hq; kcols; apply Hq; exact H. Qed.
Lemma k_table : forall r, Cq (SQ_Table T r). Proof. kcols; reflexivity. Qed.
Lemma k_set : forall o sq q1 q2, Cq q1 -> Cq q2 -> Cq (SQ_Set o sq q1 q2).
Proof. intros o sq q1 q2 H1 H2; kcols; rewrite map_app, (H1 ce' ce H), (H2 ce' ce H); reflexivity. Qed.
Lemma k_select : forall sp, Cs sp -> Cq (SQ_Select sp). Proof. intros sp Hs; kcols; apply Hs; exact H. Qed.
Lemma k_order : forall q lo off lim, Cq q -> (forall sp, q = SQ_Select sp -> Cs sp) -> LO T relname Ce lo -> Cq (SQ_Order q lo off lim).
Proof. intros q lo off lim Hq _ _; kcols; apply Hq; exact H. Qed.
Lemma k_fetch : forall q lo off ties pct n, Cq q -> (forall sp, q = SQ_Select sp -> Cs sp) -> LO T relname Ce lo ->
  Cq (SQ_Fetch q lo off ties pct n).
Proof. intros q lo off ties pct n Hq _ _; kcols; apply Hq; exact H. Qed.
Lemma k_window : forall q lw, Cq q ->
  (forall f lp lo a, In (W_As f lp lo a) lw -> LE T relname Ce lp /\ LO T relname Ce lo /\ LE T relname Ce (wexprs T relname f)) ->
  Cq (SQ_Window q lw).
Proof. intros q lw Hq _; kcols; apply Hq; exact H. Qed.
Lemma k_with : forall r q1 q2, Cq q1 -> Cq q2 -> Cq (SQ_With r q1 q2).
Proof.
intros r q1 q2 H1 H2; kcols.
rewrite map_app, (H1 ce' ce H), (H2 _ _ (Rsort_cons _ _ r _ _ nil nil H (sort_rename q1 ce' ce H))); reflexivity.
Qed.
Lemma k_withrec : forall sq r q1 q2 q3, Cq q1 -> Cq q2 -> Cq q3 -> Cq (SQ_WithRec sq r q1 q2 q3).
Proof.
intros sq r q1 q2 q3 H1 H2 H3; kcols.
assert (H' := Rsort_cons _ _ r _ _ nil nil H (sort_rename q1 ce' ce H)).
rewrite !map_app, (H1 ce' ce H), (H2 _ _ H'), (H3 _ _ H'); reflexivity.
Qed.
Lemma k_spec : forall sq s lf w g h,
  match s with S_Star _ _ => True | S_List l => forall e a, In (S_As e a) l -> Ce e end ->
  (forall f, In f lf -> Cf f) -> Cc w ->
  match g with
  | G_Fine _ _ => True
  | G_By l | G_Rollup l | G_Cube l => LE T relname Ce l
  | G_Sets ss => forall l, In l ss -> LE T relname Ce l
  end -> Cc h -> Cs (Select sq s lf w g h).
Proof.
intros sq s lf w g h Hs Hf Hw Hg Hh; kcols.
assert (Hb : Fset.Union (A T) (map (sfrom_sort ORN basesort' ce') (map rf lf)) =S=
             rs (Fset.Union (A T) (map (sfrom_sort ORN basesort ce) lf))).
{ rewrite (Fset.equal_eq_2 _ _ _ _ (rs_Union _)), map_map, map_map; apply Union_eq_F2.
  clear - H Hbs Hrr Hrr' Hord; induction lf as [ | f lf IH]; constructor; [apply sort_rename_f; exact H | exact IH]. }
match goal with |- filter _ ?L' = map rho (filter _ ?L) => replace L' with (map rho L) end.
- apply filter_map_rho; intro a; rewrite (Fset.mem_eq_2 _ _ _ Hb), mem_rs; reflexivity.
- rewrite !map_app; f_equal; [ | f_equal; [ | f_equal; [ | f_equal]]].
  + destruct s as [ | l]; [reflexivity | ].
    symmetry; apply flat_map_rho; intros [e a] I; apply (Hs e a I); exact H.
  + symmetry; apply Hw; exact H.
  + destruct g as [ | l | ss | l | l]; try reflexivity; try (symmetry; apply Cflat; assumption).
    induction ss as [ | l ss IH]; [reflexivity | ]; cbn [map]; rewrite map_app, IH; [ | intros l' I; apply Hg; right; exact I].
    f_equal; symmetry; apply Cflat; [apply Hg; left; reflexivity | exact H].
  + symmetry; apply Hh; exact H.
  + symmetry; apply flat_map_rho; intros f I; apply (Hf f I); exact H.
Qed.
Lemma k_fquery : forall q r, Cq q -> Cf (Fr_Query q r). Proof. intros q r Hq; kcols; apply Hq; exact H. Qed.
Lemma k_fjoin : forall jt lat f1 f2 c, Cf f1 -> Cf f2 -> Cc c -> Cf (Fr_Join jt lat f1 f2 c).
Proof. intros jt lat f1 f2 c H1 H2 Hc; kcols; rewrite !map_app, (H1 ce' ce H), (H2 ce' ce H), (Hc ce' ce H); reflexivity. Qed.
Lemma k_ffun : forall name args ord atts, LE T relname Ce args -> Cf (Fr_Fun name args ord atts).
Proof. intros name args ord atts Ha; kcols; apply Cflat; assumption. Qed.

Lemma cols_e : forall e, Ce e.
Proof.
exact (ind_e T relname Ce Cc Cq Cs Cf k_const k_col k_fun k_agg k_aggx k_case k_cond k_sub k_grouping k_conj k_not
  k_true k_pred k_expr k_quant k_in k_exists k_table k_set k_select k_order k_fetch k_window k_with k_withrec k_spec
  k_fquery k_fjoin k_ffun).
Qed.

Lemma cols_c : forall c, Cc c.
Proof.
exact (ind_c T relname Ce Cc Cq Cs Cf k_const k_col k_fun k_agg k_aggx k_case k_cond k_sub k_grouping k_conj k_not
  k_true k_pred k_expr k_quant k_in k_exists k_table k_set k_select k_order k_fetch k_window k_with k_withrec k_spec
  k_fquery k_fjoin k_ffun).
Qed.

Lemma cols_q : forall q, Cq q.
Proof.
exact (ind_q T relname Ce Cc Cq Cs Cf k_const k_col k_fun k_agg k_aggx k_case k_cond k_sub k_grouping k_conj k_not
  k_true k_pred k_expr k_quant k_in k_exists k_table k_set k_select k_order k_fetch k_window k_with k_withrec k_spec
  k_fquery k_fjoin k_ffun).
Qed.

End Sec.
