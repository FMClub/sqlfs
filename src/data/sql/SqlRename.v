(** * Renaming the attributes (TODO 6.3, issue I4)

    The evaluation of [SqlFull.v] does not depend on the names of the attributes: for a bijection [rho] of
    the attributes which preserves their types and their affinities, and fixes the attribute of
    the failed rows, the rows of the renamed query over the renamed database are the renamed rows of the query,
    in the same order ([eval_rename]), for the whole syntax. The front end names the columns of each item of a
    [FROM] clause and of each derived table by their positions, so that the named semantics of [SqlFull.v] is a
    positional semantics in which two columns never share a name; this theorem says that the choice of the names
    does not matter.
    - The tuples: [rt], the renamed tuple; [RT t' t], [t'] is [rt t] up to the equality of tuples; [RL], lists of
      related tuples. [Hdot]: a missing attribute of a tuple has the default value of its type.
    - The syntax: [r_q] renames every attribute of a query.
    - The static functions commute with the renaming: the sorts ([sort_rename]), the columns read from outside
      ([cols_q]), the placement of the aggregates ([foreign_q], [has_agg_e]), the equality of expressions
      ([eqb_rename]).
    - The evaluation: related environments ([REnv], [RCE]) give equal values to the expressions and the
      conditions and related rows to the queries, by the induction principle of [SqlInduction.v], with one
      lemma for each operation on rows (set operations, joins, sorting, grouping, windows, [WITH RECURSIVE]). *)
Require Import List Bool Sorting ZArith NArith QArith.
Require Import BasicFacts ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection FlatData SqlFull SqlInduction
        SqlFullFacts SqlGroupFacts SqlCongruence SqlScopeQuery Bool3 Formula.
Import Tuple.

Section Sec.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.
Hypothesis ORN : Oset.Rcd relname.
Hypothesis rho : attribute T -> attribute T.
Hypothesis rhoi : attribute T -> attribute T.
Hypothesis Hrr : forall a, rhoi (rho a) = a.
Hypothesis Hrr' : forall b, rho (rhoi b) = b.
Hypothesis Hty : forall a, type_of_attribute T (rho a) = type_of_attribute T a.

Lemma rho_inj : forall a b, rho a = rho b -> a = b.
Proof. intros a b H; rewrite <- (Hrr a), <- (Hrr b), H; reflexivity. Qed.

Lemma rho_eqb : forall a b, Oset.eq_bool (OAtt T) (rho a) (rho b) = Oset.eq_bool (OAtt T) a b.
Proof.
intros a b; apply eq_true_iff_eq; rewrite !Oset.eq_bool_true_iff; split; [apply rho_inj | intro H; rewrite H; reflexivity].
Qed.

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

(** the elements of a renamed set are the renamed elements, in another order *)
Lemma in_elements_iff : forall (s : Fset.set (A T)) (x : attribute T), In x ({{{s}}}) <-> x inS s.
Proof.
intros s x; split; intro H; [apply Fset.in_elements_mem; exact H | apply Fset.mem_in_elements; exact H].
Qed.

Lemma elements_NoDup : forall s : Fset.set (A T), NoDup ({{{s}}}).
Proof.
intro s; assert (S := Fset.elements_spec3 _ s).
apply Sorted_StronglySorted in S; [ | intros x y z; apply Oset.compare_lt_trans].
induction S as [ | x l S IH F]; constructor; [ | exact IH].
intro I; rewrite Forall_forall in F; generalize (F x I); rewrite Oset.compare_eq_refl; discriminate.
Qed.

Lemma NoDup_map_inj : forall (f : attribute T -> attribute T) l, (forall a b, f a = f b -> a = b) -> NoDup l -> NoDup (map f l).
Proof.
intros f l Hf H; induction H as [ | x l Hx H IH]; simpl; constructor; [ | exact IH].
intro I; rewrite in_map_iff in I; destruct I as [y [E Iy]]; apply Hx; rewrite <- (Hf _ _ E); exact Iy.
Qed.

Lemma rhoi_inj : forall a b, rhoi a = rhoi b -> a = b.
Proof. intros a b H; rewrite <- (Hrr' a), <- (Hrr' b), H; reflexivity. Qed.

Lemma elements_length : forall s' s, s' =S= rs s -> length ({{{s'}}}) = length ({{{s}}}).
Proof.
intros s' s H; apply PeanoNat.Nat.le_antisymm.
- rewrite <- (map_length rhoi); apply NoDup_incl_length; [apply NoDup_map_inj; [exact rhoi_inj | apply elements_NoDup] | ].
  intros x Hx; rewrite in_map_iff in Hx; destruct Hx as [y [E Hy]]; subst x.
  rewrite in_elements_iff in *; rewrite (Fset.mem_eq_2 _ _ _ H), mem_rs' in Hy; exact Hy.
- rewrite <- (map_length rho); apply NoDup_incl_length; [apply NoDup_map_inj; [exact rho_inj | apply elements_NoDup] | ].
  intros x Hx; rewrite in_map_iff in Hx; destruct Hx as [y [E Hy]]; subst x.
  rewrite in_elements_iff in *; rewrite (Fset.mem_eq_2 _ _ _ H), mem_rs; exact Hy.
Qed.

Lemma existsb_elements : forall s' s (p' p : attribute T -> bool), s' =S= rs s -> (forall a, p' (rho a) = p a) ->
  existsb p' ({{{s'}}}) = existsb p ({{{s}}}).
Proof.
intros s' s p' p H K; apply eq_true_iff_eq; rewrite !existsb_exists; split; intros [x [Hx Px]].
- exists (rhoi x); rewrite in_elements_iff in *; rewrite (Fset.mem_eq_2 _ _ _ H), mem_rs' in Hx.
  split; [exact Hx | rewrite <- K, Hrr'; exact Px].
- exists (rho x); rewrite in_elements_iff in *; rewrite (Fset.mem_eq_2 _ _ _ H), mem_rs.
  split; [exact Hx | rewrite K; exact Px].
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

(** lists of related tuples *)
Definition RL := Forall2 RT.

Lemma RL_map : forall (X Y : Type) (f : X -> tuple T) (g : Y -> tuple T) (P : X -> Y -> Prop) l1 l2,
  Forall2 P l1 l2 -> (forall x y, P x y -> RT (f x) (g y)) -> RL (map f l1) (map g l2).
Proof. intros X Y f g P l1 l2 H K; induction H; constructor; auto. Qed.

Lemma RL_app : forall l1 l2 l1' l2', RL l1 l2 -> RL l1' l2' -> RL (l1 ++ l1') (l2 ++ l2').
Proof. intros; apply Forall2_app; assumption. Qed.

(** the relation as a boolean, to check a renamed database by computation *)
Fixpoint RLb (l' l : list (tuple T)) : bool :=
  match l', l with
  | nil, nil => true
  | t' :: l', t :: l => Oeset.eq_bool (OTuple T) t' (rt t) && RLb l' l
  | _, _ => false
  end.

Lemma RLb_RL : forall l' l, RLb l' l = true -> RL l' l.
Proof.
intro l'; induction l' as [ | t' l' IH]; intros [ | t l] H; try discriminate H; [constructor | ].
simpl in H; rewrite andb_true_iff in H; destruct H as [H1 H2]; constructor; [ | apply IH; exact H2].
unfold RT; unfold Oeset.eq_bool in H1; destruct (Oeset.compare (OTuple T) t' (rt t)); trivial; discriminate H1.
Qed.

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

(** the equality of the grouping expressions *)
Definition Be (x : SqlFull.sexpr T relname) := forall y, sexpr_eqb (re x) (re y) = sexpr_eqb x y.
Definition Bc (c : SqlFull.scond T relname) := forall d, scond_eqb (rc c) (rc d) = scond_eqb c d.
Definition Bt {X : Type} (x : X) := True.

Lemma eqb_list : forall l, LE T relname Be l -> forall l',
  (fix eqs (l1 l2 : list (SqlFull.sexpr T relname)) {struct l1} : bool :=
     match l1, l2 with nil, nil => true | x :: r1, y :: r2 => sexpr_eqb x y && eqs r1 r2 | _, _ => false end) (map re l) (map re l') =
  (fix eqs (l1 l2 : list (SqlFull.sexpr T relname)) {struct l1} : bool :=
     match l1, l2 with nil, nil => true | x :: r1, y :: r2 => sexpr_eqb x y && eqs r1 r2 | _, _ => false end) l l'.
Proof.
intro l; induction l as [ | x l IHl]; intros Hl [ | y l']; try reflexivity.
cbn [map]; rewrite (Hl x (or_introl eq_refl) y), IHl; [reflexivity | intros z Hz; apply Hl; right; exact Hz].
Qed.

Ltac beq y := intro y; destruct y; cbn [r_e r_c sexpr_eqb scond_eqb]; fold r_e r_c; try reflexivity.

Lemma b_const : forall v, Be (E_Const T relname v). Proof. intro v; beq y. Qed.
Lemma b_col : forall a, Be (E_Col T relname a). Proof. intro a; beq y; apply rho_eqb. Qed.
Lemma b_fun : forall f l, LE T relname Be l -> Be (E_Fun f l).
Proof. intros f l Hl; beq y; f_equal; apply eqb_list; exact Hl. Qed.
Lemma b_agg : forall ag sq e c, Be e -> Bc c -> Be (E_Agg ag sq e c). Proof. intros ag sq e c _ _; beq y. Qed.
Lemma b_aggx : forall ag sq e sep lo c, Be e -> (forall s, sep = Some s -> Be s) -> LO T relname Be lo -> Bc c ->
  Be (E_AggX ag sq e sep lo c).
Proof. intros ag sq e sep lo c _ _ _ _; beq y. Qed.
Lemma b_case : forall c e1 e2, Bc c -> Be e1 -> Be e2 -> Be (E_Case c e1 e2).
Proof. intros c e1 e2 Hc H1 H2; beq y; rewrite Hc, H1, H2; reflexivity. Qed.
Lemma b_cond : forall c, Bc c -> Be (E_Cond c). Proof. intros c Hc; beq y; apply Hc. Qed.
Lemma b_sub : forall q, @Bt (SqlFull.squery T relname) q -> Be (E_Sub q). Proof. intros q _; beq y. Qed.
Lemma b_grouping : forall x, Be x -> Be (E_Grouping x). Proof. intros x _; beq y. Qed.
Lemma b_conj : forall a c1 c2, Bc c1 -> Bc c2 -> Bc (C_Conj a c1 c2).
Proof. intros a c1 c2 H1 H2; beq d; rewrite H1, H2; reflexivity. Qed.
Lemma b_not : forall c, Bc c -> Bc (C_Not c). Proof. intros c Hc; beq d; apply Hc. Qed.
Lemma b_true : Bc (C_True T relname). Proof. beq d. Qed.
Lemma b_pred : forall p l, LE T relname Be l -> Bc (C_Pred p l).
Proof. intros p l Hl; beq d; f_equal; apply eqb_list; exact Hl. Qed.
Lemma b_expr : forall e, Be e -> Bc (C_Expr e). Proof. intros e He; beq d; apply He. Qed.
Lemma b_quant : forall qtf p l q la, LE T relname Be l -> @Bt (SqlFull.squery T relname) q -> Bc (C_Quant qtf p l q la).
Proof. intros qtf p l q la _ _; beq d. Qed.
Lemma b_in : forall l q la, LE T relname Be l -> @Bt (SqlFull.squery T relname) q -> Bc (C_In l q la).
Proof. intros l q la _ _; beq d. Qed.
Lemma b_exists : forall q, @Bt (SqlFull.squery T relname) q -> Bc (C_Exists q). Proof. intros q _; beq d. Qed.

Lemma eqb_rename : forall x y : SqlFull.sexpr T relname, sexpr_eqb (re x) (re y) = sexpr_eqb x y.
Proof.
refine (ind_e T relname Be Bc Bt Bt Bt b_const b_col b_fun b_agg b_aggx b_case b_cond b_sub b_grouping b_conj b_not
  b_true b_pred b_expr b_quant b_in b_exists _ _ _ _ _ _ _ _ _ _ _ _); intros; exact I.
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
  clear - H Hbs Hrr Hrr'; induction lf as [ | f lf IH]; constructor; [apply sort_rename_f; exact H | exact IH]. }
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

(** the aggregates of the blocks *)
Lemma existsb_map_rho : forall (p p' : attribute T -> bool) l, (forall a, p' (rho a) = p a) ->
  existsb p' (map rho l) = existsb p l.
Proof. intros p p' l H; induction l as [ | a l IH]; [reflexivity | simpl; rewrite H, IH; reflexivity]. Qed.

Lemma cols_test : forall (l : list (attribute T)) (sa' sa : Fset.set (A T)) (X : bool),
  sa' =S= rs sa ->
  match map rho l with nil => X | y :: r => existsb (fun x => x inS? sa') (y :: r) end =
  match l with nil => X | y :: r => existsb (fun x => x inS? sa) (y :: r) end.
Proof.
intros l sa' sa X H; destruct l as [ | a l]; [reflexivity | ].
rewrite <- (existsb_map_rho (fun x => x inS? sa) (fun x => x inS? sa') (a :: l)); [reflexivity | ].
intro b; rewrite (Fset.mem_eq_2 _ _ _ H), mem_rs; reflexivity.
Qed.

Lemma cols_test2 : forall (l : list (attribute T)) (sa' sa b' b : Fset.set (A T)),
  sa' =S= rs sa -> b' =S= rs b ->
  match map rho l with nil => false | y :: r => existsb (fun x => x inS? sa') (y :: r) && negb (existsb (fun x => x inS? b') (y :: r)) end =
  match l with nil => false | y :: r => existsb (fun x => x inS? sa) (y :: r) && negb (existsb (fun x => x inS? b) (y :: r)) end.
Proof.
intros l sa' sa b' b H1 H2; destruct l as [ | a l]; [reflexivity | ].
rewrite <- (existsb_map_rho (fun x => x inS? sa) (fun x => x inS? sa') (a :: l)),
  <- (existsb_map_rho (fun x => x inS? b) (fun x => x inS? b') (a :: l)); [reflexivity | | ];
  intro c; [rewrite (Fset.mem_eq_2 _ _ _ H2) | rewrite (Fset.mem_eq_2 _ _ _ H1)]; rewrite mem_rs; reflexivity.
Qed.

Definition spf (ce : SqlFull.cte_env T relname) bs (sa : Fset.set (A T)) (sp : SqlFull.sspec T relname) : bool :=
  squery_foreign ORN bs ce sa (SQ_Select sp).

Definition Fe (e : SqlFull.sexpr T relname) := forall ce' ce sa' sa b' b, Rsort ce' ce -> sa' =S= rs sa -> b' =S= rs b ->
  sexpr_foreign ORN basesort' ce' sa' b' (re e) = sexpr_foreign ORN basesort ce sa b e.
Definition Fc (c : SqlFull.scond T relname) := forall ce' ce sa' sa b' b, Rsort ce' ce -> sa' =S= rs sa -> b' =S= rs b ->
  scond_foreign ORN basesort' ce' sa' b' (rc c) = scond_foreign ORN basesort ce sa b c.
Definition Fq (q : SqlFull.squery T relname) := forall ce' ce sa' sa, Rsort ce' ce -> sa' =S= rs sa ->
  squery_foreign ORN basesort' ce' sa' (rq q) = squery_foreign ORN basesort ce sa q.
Definition Fs (sp : SqlFull.sspec T relname) := forall ce' ce sa' sa, Rsort ce' ce -> sa' =S= rs sa ->
  spf ce' basesort' sa' (rsp sp) = spf ce basesort sa sp.
Definition Ff (f : SqlFull.sfrom T relname) := True.

Ltac fold_for ce' ce :=
  fold (sexpr_foreign ORN basesort' ce') (sexpr_foreign ORN basesort ce) (scond_foreign ORN basesort' ce')
       (scond_foreign ORN basesort ce) (squery_foreign ORN basesort' ce') (squery_foreign ORN basesort ce).

Ltac kfor := intros; intros ce' ce sa' sa b' b H Hs Hb;
  cbn [r_e r_c r_q r_s r_f sexpr_foreign scond_foreign squery_foreign]; fold_for ce' ce; fold_cols ce' ce.
Ltac kforq := intros; intros ce' ce sa' sa H Hs;
  cbn [r_e r_c r_q r_s r_f sexpr_foreign scond_foreign squery_foreign]; fold_for ce' ce; fold_cols ce' ce.

Lemma existsb_F : forall (X : Type) (f : X -> X) (p p' : X -> bool) l, (forall x, In x l -> p' (f x) = p x) ->
  existsb p' (map f l) = existsb p l.
Proof. intros X f p p' l H; induction l as [ | x l IH]; [reflexivity | simpl; rewrite H, IH; [reflexivity | | left; reflexivity]]; intros; apply H; right; assumption. Qed.

Lemma f_const : forall v, Fe (E_Const T relname v). Proof. kfor; reflexivity. Qed.
Lemma f_col : forall a, Fe (E_Col T relname a). Proof. kfor; reflexivity. Qed.
Lemma f_fun : forall f l, LE T relname Fe l -> Fe (E_Fun f l).
Proof. intros f l Hl; kfor; apply existsb_F; intros x Ix; apply (Hl x Ix); assumption. Qed.
Lemma f_agg : forall ag sq e c, Fe e -> Fc c -> Fe (E_Agg ag sq e c).
Proof.
intros ag sq e c _ _; kfor; rewrite (cols_e e ce' ce H), (cols_c c ce' ce H), <- map_app.
apply cols_test2; assumption.
Qed.
Lemma f_aggx : forall ag sq e sep lo c, Fe e -> (forall s, sep = Some s -> Fe s) -> LO T relname Fe lo -> Fc c ->
  Fe (E_AggX ag sq e sep lo c).
Proof.
intros ag sq e sep lo c _ _ _ _; kfor.
rewrite (cols_e e ce' ce H), (cols_c c ce' ce H), (Cflat_o lo ce' ce (fun x d n _ => cols_e x) H).
replace (match match sep with Some s => Some (re s) | None => None end with Some s => sc_e' ce' s | None => nil end)
  with (map rho (match sep with Some s => sc_e ce s | None => nil end))
  by (destruct sep as [x | ]; [symmetry; apply cols_e; exact H | reflexivity]).
rewrite <- !map_app; apply cols_test2; assumption.
Qed.
Lemma f_case : forall c e1 e2, Fc c -> Fe e1 -> Fe e2 -> Fe (E_Case c e1 e2).
Proof. intros c e1 e2 Hc H1 H2; kfor; rewrite (Hc ce' ce sa' sa b' b), (H1 ce' ce sa' sa b' b), (H2 ce' ce sa' sa b' b); auto. Qed.
Lemma f_cond : forall c, Fc c -> Fe (E_Cond c). Proof. intros c Hc; kfor; apply Hc; assumption. Qed.
Lemma f_sub : forall q, Fq q -> Fe (E_Sub q). Proof. intros q Hq; kfor; apply Hq; assumption. Qed.
Lemma f_grouping : forall x, Fe x -> Fe (E_Grouping x). Proof. intros x Hx; kfor; apply Hx; assumption. Qed.
Lemma f_conj : forall a c1 c2, Fc c1 -> Fc c2 -> Fc (C_Conj a c1 c2).
Proof. intros a c1 c2 H1 H2; kfor; rewrite (H1 ce' ce sa' sa b' b), (H2 ce' ce sa' sa b' b); auto. Qed.
Lemma f_not : forall c, Fc c -> Fc (C_Not c). Proof. intros c Hc; kfor; apply Hc; assumption. Qed.
Lemma f_true : Fc (C_True T relname). Proof. kfor; reflexivity. Qed.
Lemma f_pred : forall p l, LE T relname Fe l -> Fc (C_Pred p l).
Proof. intros p l Hl; kfor; apply existsb_F; intros x Ix; apply (Hl x Ix); assumption. Qed.
Lemma f_expr : forall e, Fe e -> Fc (C_Expr e). Proof. intros e He; kfor; apply He; assumption. Qed.
Lemma f_quant : forall qtf p l q la, LE T relname Fe l -> Fq q -> Fc (C_Quant qtf p l q la).
Proof.
intros qtf p l q la Hl Hq; kfor; rewrite (Hq ce' ce sa' sa H Hs); f_equal.
apply existsb_F; intros x Ix; apply (Hl x Ix); assumption.
Qed.
Lemma f_in : forall l q la, LE T relname Fe l -> Fq q -> Fc (C_In l q la).
Proof.
intros l q la Hl Hq; kfor; rewrite (Hq ce' ce sa' sa H Hs); f_equal.
apply existsb_F; intros x Ix; apply (Hl x Ix); assumption.
Qed.
Lemma f_exists : forall q, Fq q -> Fc (C_Exists q). Proof. intros q Hq; kfor; apply Hq; assumption. Qed.
Lemma f_table : forall r, Fq (SQ_Table T r). Proof. kforq; reflexivity. Qed.
Lemma f_set : forall o sq q1 q2, Fq q1 -> Fq q2 -> Fq (SQ_Set o sq q1 q2).
Proof. intros o sq q1 q2 H1 H2; kforq; rewrite (H1 ce' ce sa' sa H Hs), (H2 ce' ce sa' sa H Hs); reflexivity. Qed.
Lemma f_select : forall sp, Fs sp -> Fq (SQ_Select sp). Proof. intros sp Hsp ce' ce sa' sa H Hs; exact (Hsp ce' ce sa' sa H Hs). Qed.
Lemma f_order : forall q lo off lim, Fq q -> (forall sp, q = SQ_Select sp -> Fs sp) -> LO T relname Fe lo -> Fq (SQ_Order q lo off lim).
Proof. intros q lo off lim Hq _ _; kforq; apply Hq; assumption. Qed.
Lemma f_fetch : forall q lo off ties pct n, Fq q -> (forall sp, q = SQ_Select sp -> Fs sp) -> LO T relname Fe lo ->
  Fq (SQ_Fetch q lo off ties pct n).
Proof. intros q lo off ties pct n Hq _ _; kforq; apply Hq; assumption. Qed.
Lemma f_window : forall q lw, Fq q ->
  (forall f lp lo a, In (W_As f lp lo a) lw -> LE T relname Fe lp /\ LO T relname Fe lo /\ LE T relname Fe (wexprs T relname f)) ->
  Fq (SQ_Window q lw).
Proof. intros q lw Hq _; kforq; apply Hq; assumption. Qed.
Lemma f_with : forall r q1 q2, Fq q1 -> Fq q2 -> Fq (SQ_With r q1 q2).
Proof.
intros r q1 q2 H1 H2; kforq.
rewrite (H1 ce' ce sa' sa H Hs), (H2 _ _ sa' sa (Rsort_cons _ _ r _ _ nil nil H (sort_rename q1 ce' ce H)) Hs); reflexivity.
Qed.
Lemma f_withrec : forall sq r q1 q2 q3, Fq q1 -> Fq q2 -> Fq q3 -> Fq (SQ_WithRec sq r q1 q2 q3).
Proof.
intros sq r q1 q2 q3 H1 H2 H3; kforq.
assert (H' := Rsort_cons _ _ r _ _ nil nil H (sort_rename q1 ce' ce H)).
rewrite (H1 ce' ce sa' sa H Hs), (H2 _ _ sa' sa H' Hs), (H3 _ _ sa' sa H' Hs); reflexivity.
Qed.
Lemma f_spec : forall sq s lf w g h,
  match s with S_Star _ _ => True | S_List l => forall e a, In (S_As e a) l -> Fe e end ->
  (forall f, In f lf -> Ff f) -> Fc w ->
  match g with
  | G_Fine _ _ => True
  | G_By l | G_Rollup l | G_Cube l => LE T relname Fe l
  | G_Sets ss => forall l, In l ss -> LE T relname Fe l
  end -> Fc h -> Fs (Select sq s lf w g h).
Proof.
intros sq s lf w g h Hs' _ Hw _ Hh ce' ce sa' sa H Hs; unfold spf; cbn [r_s squery_foreign]; fold_for ce' ce.
assert (Hb : Fset.Union (A T) (map (sfrom_sort ORN basesort' ce') (map rf lf)) =S=
             rs (Fset.Union (A T) (map (sfrom_sort ORN basesort ce) lf))).
{ rewrite (Fset.equal_eq_2 _ _ _ _ (rs_Union _)), map_map, map_map; apply Union_eq_F2.
  clear - H Hbs Hrr Hrr'; induction lf as [ | f lf IH]; constructor; [apply sort_rename_f; exact H | exact IH]. }
rewrite (Hh _ _ _ _ _ _ H Hs Hb), (Hw _ _ _ _ _ _ H Hs Hb); f_equal; f_equal.
destruct s as [ | l]; [reflexivity | ].
rewrite map_map; apply existsb_F; intros [e a] I; cbn beta iota; apply (Hs' e a I); [assumption | assumption | rewrite <- (map_map rf); exact Hb].
Qed.
Lemma f_fquery : forall q r, Fq q -> Ff (Fr_Query q r). Proof. intros; exact I. Qed.
Lemma f_fjoin : forall jt lat f1 f2 c, Ff f1 -> Ff f2 -> Fc c -> Ff (Fr_Join jt lat f1 f2 c). Proof. intros; exact I. Qed.
Lemma f_ffun : forall name args ord atts, LE T relname Fe args -> Ff (Fr_Fun name args ord atts). Proof. intros; exact I. Qed.

Lemma foreign_q : forall q, Fq q.
Proof.
exact (ind_q T relname Fe Fc Fq Fs Ff f_const f_col f_fun f_agg f_aggx f_case f_cond f_sub f_grouping f_conj f_not
  f_true f_pred f_expr f_quant f_in f_exists f_table f_set f_select f_order f_fetch f_window f_with f_withrec f_spec
  f_fquery f_fjoin f_ffun).
Qed.

Definition He_ (e : SqlFull.sexpr T relname) := forall ce' ce sa' sa, Rsort ce' ce -> sa' =S= rs sa ->
  sexpr_has_agg ORN basesort' ce' sa' (re e) = sexpr_has_agg ORN basesort ce sa e.
Definition Hc_ (c : SqlFull.scond T relname) := forall ce' ce sa' sa, Rsort ce' ce -> sa' =S= rs sa ->
  scond_has_agg ORN basesort' ce' sa' (rc c) = scond_has_agg ORN basesort ce sa c.
Definition Ht_ {X : Type} (x : X) := True.

Ltac khas := intros ce' ce sa' sa H Hs;
  cbn [r_e r_c sexpr_has_agg scond_has_agg];
  fold (sexpr_has_agg ORN basesort' ce' sa') (sexpr_has_agg ORN basesort ce sa)
       (scond_has_agg ORN basesort' ce' sa') (scond_has_agg ORN basesort ce sa); fold_cols ce' ce.

Lemma h_const : forall v, He_ (E_Const T relname v). Proof. intro v; khas; reflexivity. Qed.
Lemma h_col : forall a, He_ (E_Col T relname a). Proof. intro a; khas; reflexivity. Qed.
Lemma h_fun : forall f l, LE T relname He_ l -> He_ (E_Fun f l).
Proof. intros f l Hl; khas; apply existsb_F; intros x Ix; apply (Hl x Ix); assumption. Qed.
Lemma h_agg : forall ag sq e c, He_ e -> Hc_ c -> He_ (E_Agg ag sq e c).
Proof. intros ag sq e c _ _; khas; rewrite (cols_e e ce' ce H), (cols_c c ce' ce H), <- map_app; apply cols_test; exact Hs. Qed.
Lemma h_aggx : forall ag sq e sep lo c, He_ e -> (forall s, sep = Some s -> He_ s) -> LO T relname He_ lo -> Hc_ c ->
  He_ (E_AggX ag sq e sep lo c).
Proof.
intros ag sq e sep lo c _ _ _ _; khas.
rewrite (cols_e e ce' ce H), (cols_c c ce' ce H), (Cflat_o lo ce' ce (fun x d n _ => cols_e x) H).
replace (match match sep with Some s => Some (re s) | None => None end with Some s => sc_e' ce' s | None => nil end)
  with (map rho (match sep with Some s => sc_e ce s | None => nil end))
  by (destruct sep as [x | ]; [symmetry; apply cols_e; exact H | reflexivity]).
rewrite <- !map_app; apply cols_test; exact Hs.
Qed.
Lemma h_case : forall c e1 e2, Hc_ c -> He_ e1 -> He_ e2 -> He_ (E_Case c e1 e2).
Proof. intros c e1 e2 Hc H1 H2; khas; rewrite (Hc ce' ce sa' sa), (H1 ce' ce sa' sa), (H2 ce' ce sa' sa); auto. Qed.
Lemma h_cond : forall c, Hc_ c -> He_ (E_Cond c). Proof. intros c Hc; khas; apply Hc; assumption. Qed.
Lemma h_sub : forall q, @Ht_ (SqlFull.squery T relname) q -> He_ (E_Sub q). Proof. intros q _; khas; apply foreign_q; assumption. Qed.
Lemma h_grouping : forall x, He_ x -> He_ (E_Grouping x). Proof. intros x _; khas; reflexivity. Qed.
Lemma h_conj : forall a c1 c2, Hc_ c1 -> Hc_ c2 -> Hc_ (C_Conj a c1 c2).
Proof. intros a c1 c2 H1 H2; khas; rewrite (H1 ce' ce sa' sa), (H2 ce' ce sa' sa); auto. Qed.
Lemma h_not : forall c, Hc_ c -> Hc_ (C_Not c). Proof. intros c Hc; khas; apply Hc; assumption. Qed.
Lemma h_true : Hc_ (C_True T relname). Proof. khas; reflexivity. Qed.
Lemma h_pred : forall p l, LE T relname He_ l -> Hc_ (C_Pred p l).
Proof. intros p l Hl; khas; apply existsb_F; intros x Ix; apply (Hl x Ix); assumption. Qed.
Lemma h_expr : forall e, He_ e -> Hc_ (C_Expr e). Proof. intros e He; khas; apply He; assumption. Qed.
Lemma h_quant : forall qtf p l q la, LE T relname He_ l -> @Ht_ (SqlFull.squery T relname) q -> Hc_ (C_Quant qtf p l q la).
Proof.
intros qtf p l q la Hl _; khas; rewrite (foreign_q q ce' ce sa' sa H Hs); f_equal.
apply existsb_F; intros x Ix; apply (Hl x Ix); assumption.
Qed.
Lemma h_in : forall l q la, LE T relname He_ l -> @Ht_ (SqlFull.squery T relname) q -> Hc_ (C_In l q la).
Proof.
intros l q la Hl _; khas; rewrite (foreign_q q ce' ce sa' sa H Hs); f_equal.
apply existsb_F; intros x Ix; apply (Hl x Ix); assumption.
Qed.
Lemma h_exists : forall q, @Ht_ (SqlFull.squery T relname) q -> Hc_ (C_Exists q). Proof. intros q _; khas; apply foreign_q; assumption. Qed.

Lemma has_agg_e : forall e, He_ e.
Proof.
refine (ind_e T relname He_ Hc_ Ht_ Ht_ Ht_ h_const h_col h_fun h_agg h_aggx h_case h_cond h_sub h_grouping h_conj h_not
  h_true h_pred h_expr h_quant h_in h_exists _ _ _ _ _ _ _ _ _ _ _ _); intros; exact I.
Qed.

Lemma has_agg_c : forall c, Hc_ c.
Proof.
refine (ind_c T relname He_ Hc_ Ht_ Ht_ Ht_ h_const h_col h_fun h_agg h_aggx h_case h_cond h_sub h_grouping h_conj h_not
  h_true h_pred h_expr h_quant h_in h_exists _ _ _ _ _ _ _ _ _ _ _ _); intros; exact I.
Qed.


(** * The evaluation of the renamed queries *)

Hypothesis O : dialect T.
(** the renaming preserves the affinities of the attributes, and the attribute of the failed rows *)
Hypothesis Haff : forall a, attr_affinity O (rho a) = attr_affinity O a.
Hypothesis Herr : rho (err_attr O) = err_attr O.
Hypothesis instance instance' : relname -> Febag.bag (Fecol.CBag (Tuple.CTuple T)).
(** the renamed database: the rows of each table are renamed, in the same order *)
Hypothesis Hinst : forall r, RL (Febag.elements _ (instance' r)) (Febag.elements _ (instance r)).

(** ** Lists *)

Lemma F2_eq_map : forall (X Y Z : Type) (P : X -> Y -> Prop) (f : X -> Z) (g : Y -> Z) l1 l2,
  Forall2 P l1 l2 -> (forall x y, P x y -> f x = g y) -> map f l1 = map g l2.
Proof. intros X Y Z P f g l1 l2 H K; induction H; simpl; [reflexivity | rewrite (K _ _ H), IHForall2; reflexivity]. Qed.

Lemma F2_existsb : forall (X Y : Type) (P : X -> Y -> Prop) (f : X -> bool) (g : Y -> bool) l1 l2,
  Forall2 P l1 l2 -> (forall x y, P x y -> f x = g y) -> existsb f l1 = existsb g l2.
Proof. intros X Y P f g l1 l2 H K; induction H; simpl; [reflexivity | rewrite (K _ _ H), IHForall2; reflexivity]. Qed.

Lemma F2_flat_map : forall (X Y X' Y' : Type) (P : X -> Y -> Prop) (Q : X' -> Y' -> Prop) f g l1 l2,
  Forall2 P l1 l2 -> (forall x y, P x y -> Forall2 Q (f x) (g y)) -> Forall2 Q (flat_map f l1) (flat_map g l2).
Proof. intros X Y X' Y' P Q f g l1 l2 H K; induction H; simpl; [constructor | apply Forall2_app; auto]. Qed.

Lemma F2_quant : forall (X Y : Type) (P : X -> Y -> Prop) qtf f g l1 l2,
  Forall2 P l1 l2 -> (forall x y, P x y -> f x = g y) -> interp_quant (B T) qtf f l1 = interp_quant (B T) qtf g l2.
Proof.
intros X Y P qtf f g l1 l2 H K; destruct qtf; simpl;
  induction H; simpl; [reflexivity | rewrite (K _ _ H), IHForall2; reflexivity | reflexivity | rewrite (K _ _ H), IHForall2; reflexivity].
Qed.

Lemma F2_fold_left : forall (X Y X' Y' : Type) (P : X -> Y -> Prop) (Q : X' -> Y' -> Prop) f g l1 l2 a1 a2,
  Forall2 Q l1 l2 -> P a1 a2 -> (forall a1 a2 x1 x2, P a1 a2 -> Q x1 x2 -> P (f a1 x1) (g a2 x2)) ->
  P (fold_left f l1 a1) (fold_left g l2 a2).
Proof. intros X Y X' Y' P Q f g l1 l2 a1 a2 H; revert a1 a2; induction H; intros a1 a2 Ha K; simpl; auto. Qed.

Lemma existsb_map' : forall (X Y : Type) (f : X -> Y) (p : Y -> bool) l, existsb p (map f l) = existsb (fun x => p (f x)) l.
Proof. intros X Y f p l; induction l as [ | x l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma existsb_ext' : forall (X : Type) (f g : X -> bool) l, (forall x, f x = g x) -> existsb f l = existsb g l.
Proof. intros X f g l H; induction l as [ | x l IH]; simpl; [reflexivity | rewrite H, IH; reflexivity]. Qed.

Lemma existsb_eqb_re : forall e l, existsb (sexpr_eqb (re e)) (map re l) = existsb (sexpr_eqb e) l.
Proof. intros e l; rewrite existsb_map'; apply existsb_ext'; intro x; apply eqb_rename. Qed.

(** ** Tuples *)

Lemma null_of_rho : forall a, null_of T (rho a) = null_of T a.
Proof. intro a; unfold null_of; rewrite Hty; reflexivity. Qed.

Lemma store_rho : forall a v, store O (rho a) v = store O a v.
Proof. intros a v; unfold store; rewrite null_of_rho; reflexivity. Qed.

Lemma RS_union : forall s1' s1 s2' s2, s1' =S= rs s1 -> s2' =S= rs s2 -> (s1' unionS s2') =S= rs (s1 unionS s2).
Proof.
intros s1' s1 s2' s2 H1 H2; rewrite Fset.equal_spec; intro b.
rewrite Fset.mem_union, mem_rs', Fset.mem_union, (Fset.mem_eq_2 _ _ _ H1), (Fset.mem_eq_2 _ _ _ H2), !mem_rs'; reflexivity.
Qed.

Lemma RS_err : Fset.singleton (A T) (err_attr O) =S= rs (Fset.singleton (A T) (err_attr O)).
Proof.
rewrite Fset.equal_spec; intro b; rewrite mem_rs', !Fset.singleton_spec.
rewrite <- (Hrr' b) at 1; rewrite <- Herr at 1; rewrite rho_eqb; reflexivity.
Qed.

Lemma row_error_RT : forall t' t, RT t' t -> row_error O t' = row_error O t.
Proof.
intros t' t H; unfold row_error; apply existsb_elements; [apply RT_labels; exact H | ].
intro a; rewrite (RT_dot_all _ _ _ H); reflexivity.
Qed.

Lemma err_row_RT : forall t' t, RT t' t -> RT (err_row O t') (err_row O t).
Proof. intros t' t H; unfold err_row; apply RT_mk_tuple; [apply RS_union; [apply RT_labels; exact H | apply RS_err] | reflexivity]. Qed.

Lemma null_tuple_RT : forall s' s, s' =S= rs s -> RT (null_tuple T s') (null_tuple T s).
Proof. intros s' s H; unfold null_tuple; apply RT_mk_tuple; [exact H | intros; apply null_of_rho]. Qed.

Lemma canon_RT : forall t' t, RT t' t -> RT (canon_tuple O t') (canon_tuple O t).
Proof.
intros t' t H; unfold canon_tuple; apply RT_mk_tuple; [apply RT_labels; exact H | ].
intros a _; rewrite (RT_dot_all _ _ _ H); reflexivity.
Qed.

Lemma keep_errors_R : forall r' r all' all, RL r' r -> RL all' all -> RL (keep_errors O r' all') (keep_errors O r all).
Proof.
intros r' r all' all H K; unfold keep_errors.
rewrite (F2_existsb _ _ _ _ _ _ _ H row_error_RT); destruct (existsb (row_error O) r); [exact H | ].
apply RL_app; [exact H | ]; apply (F2_map2 _ _ _ _ _ RT); [ | apply err_row_RT].
apply F2_filter; [exact K | apply row_error_RT].
Qed.

Lemma tuple_count_R : forall t' t l' l, RT t' t -> RL l' l -> tuple_count O t' l' = tuple_count O t l.
Proof.
intros t' t l' l H K; unfold tuple_count; apply (F2_length _ _ RT); apply F2_filter; [exact K | ].
intros x y Hxy; apply RT_eq_bool; apply canon_RT; assumption.
Qed.

Lemma tuple_mem_R : forall t' t l' l, RT t' t -> RL l' l -> tuple_mem O t' l' = tuple_mem O t l.
Proof.
intros t' t l' l H K; unfold tuple_mem.
induction K as [ | x' x l' l Hx K IH]; [reflexivity | ]; simpl; rewrite IH; f_equal.
apply RT_eq_bool; apply canon_RT; assumption.
Qed.

Lemma F2_dedup_rec : forall (X Y : Type) (P : X -> Y -> Prop) (f : X -> tuple T) (g : Y -> tuple T),
  (forall x y, P x y -> RT (f x) (g y)) -> forall l1 l2 s1 s2, Forall2 P l1 l2 -> RL s1 s2 ->
  Forall2 P (dedup_rec O f s1 l1) (dedup_rec O g s2 l2).
Proof.
intros X Y P f g K l1 l2 s1 s2 H; revert s1 s2; induction H as [ | x y l1 l2 Hxy H IH]; intros s1 s2 Hs; simpl; [constructor | ].
rewrite (tuple_mem_R _ _ _ _ (K _ _ Hxy) Hs); destruct (tuple_mem O (g y) s2); [apply IH; exact Hs | ].
constructor; [exact Hxy | apply IH; constructor; [apply K; exact Hxy | exact Hs]].
Qed.

Lemma F2_dedup_on : forall (X Y : Type) (P : X -> Y -> Prop) (f : X -> tuple T) (g : Y -> tuple T),
  (forall x y, P x y -> RT (f x) (g y)) -> forall l1 l2, Forall2 P l1 l2 -> Forall2 P (dedup_on O f l1) (dedup_on O g l2).
Proof. intros; rewrite !dedup_on_rec; apply F2_dedup_rec; [assumption | assumption | constructor]. Qed.

Lemma RL_dedup' : forall l' l, RL l' l -> RL (dedup O l') (dedup O l).
Proof. intros l' l H; unfold dedup; apply F2_dedup_on; [intros; assumption | exact H]. Qed.

Lemma RL_filter_occ : forall k1 k2, (forall i t' t, RT t' t -> k1 i t' = k2 i t) ->
  forall l' l b' b, RL l' l -> RL b' b -> RL (filter_occ O k1 b' l') (filter_occ O k2 b l).
Proof.
intros k1 k2 K l' l b' b H; revert b' b; induction H as [ | x' x l' l Hx H IH]; intros b' b Hb; simpl; [constructor | ].
apply RL_app; [ | apply IH; constructor; assumption].
rewrite (tuple_count_R _ _ _ _ Hx Hb), (K _ _ _ Hx); destruct (k2 (tuple_count O x b) x); constructor; [exact Hx | constructor].
Qed.

Lemma set_op_R : forall o sq l1' l1 l2' l2, RL l1' l1 -> RL l2' l2 ->
  RL (eval_set_op O o sq l1' l2') (eval_set_op O o sq l1 l2).
Proof.
intros o sq l1' l1 l2' l2 H1 H2; destruct sq; destruct o; unfold eval_set_op;
  try (apply RL_dedup'; apply RL_app; assumption).
- apply RL_app; assumption.
- apply RL_app; [exact H1 | ]; apply RL_filter_occ; [ | exact H2 | constructor].
  intros i t' t H; rewrite (tuple_count_R _ _ _ _ H H1); reflexivity.
- apply RL_filter_occ; [ | exact H1 | constructor]; intros i t' t H; rewrite (tuple_count_R _ _ _ _ H H2); reflexivity.
- apply RL_filter_occ; [ | exact H1 | constructor]; intros i t' t H; rewrite (tuple_count_R _ _ _ _ H H2); reflexivity.
- apply F2_filter; [apply RL_dedup'; exact H1 | intros x y Hxy; rewrite (tuple_mem_R _ _ _ _ Hxy H2); reflexivity].
- apply F2_filter; [apply RL_dedup'; exact H1 | intros x y Hxy; rewrite (tuple_mem_R _ _ _ _ Hxy H2); reflexivity].
Qed.

Lemma F2_combine_seq : forall (X Y : Type) (P : X -> Y -> Prop) n l1 l2, Forall2 P l1 l2 ->
  Forall2 (fun x y => fst x = fst y /\ P (snd x) (snd y)) (combine (seq n (List.length l1)) l1) (combine (seq n (List.length l2)) l2).
Proof.
intros X Y P n l1 l2 H; revert n; induction H as [ | x y l1 l2 Hxy H IH]; intro n; simpl; constructor; [split; trivial | apply IH].
Qed.

Lemma find_col : forall (U : attribute T -> list (value T)) atts x,
  find (fun c : attribute T * list (value T) => Oset.eq_bool (OAtt T) (fst c) x) (map (fun a => (a, U a)) atts) =
  if Oset.mem_bool (OAtt T) x atts then Some (x, U x) else None.
Proof.
intros U atts x; induction atts as [ | b atts IH]; [reflexivity | ]; simpl.
rewrite (Oset.eq_bool_sym (OAtt T) x b); case_eq (Oset.eq_bool (OAtt T) b x); intro E; [ | exact IH].
rewrite Oset.eq_bool_true_iff in E; subst b; reflexivity.
Qed.

Lemma unify_rows_R : forall s' s l' l, s' =S= rs s -> RL l' l -> RL (unify_rows O ({{{s'}}}) l') (unify_rows O ({{{s}}}) l).
Proof.
intros s' s l' l Hs H; unfold unify_rows.
apply (F2_map2 _ _ _ _ _ _ _ _ _ _ (F2_combine_seq _ _ _ 0 _ _ H)).
intros [i t'] [j t] [E Ht]; simpl in E, Ht; subst j; apply RT_mk_tuple; [apply RT_labels; exact Ht | ].
intros a _; rewrite (RT_dot_all _ _ _ Ht).
rewrite (find_col (fun a => unify_column O (map (fun t => dot T t a) l'))), (find_col (fun a => unify_column O (map (fun t => dot T t a) l))).
rewrite <- !Fset.mem_elements, (Fset.mem_eq_2 _ _ _ Hs), mem_rs; destruct (a inS? s); [ | reflexivity].
rewrite (F2_eq_map _ _ _ _ (fun t => dot T t (rho a)) (fun t => dot T t a) _ _ H); [reflexivity | ].
intros; apply RT_dot_all; assumption.
Qed.

(** grouping *)
Lemma F2_group_insert : forall (X Y : Type) (P : X -> Y -> Prop) k x y gs1 gs2, P x y ->
  Forall2 (fun p q => fst p = fst q /\ Forall2 P (snd p) (snd q)) gs1 gs2 ->
  Forall2 (fun p q => fst p = fst q /\ Forall2 P (snd p) (snd q)) (group_insert O k x gs1) (group_insert O k y gs2).
Proof.
intros X Y P k x y gs1 gs2 Hxy H; induction H as [ | [k1 g1] [k2 g2] gs1 gs2 [E Hg] H IH]; simpl in *.
- constructor; [split; [reflexivity | constructor; [exact Hxy | constructor]] | constructor].
- subst k2; destruct (key_eqb O k k1).
  + constructor; [split; [reflexivity | apply Forall2_app; [exact Hg | constructor; [exact Hxy | constructor]]] | exact H].
  + constructor; [split; [reflexivity | exact Hg] | exact IH].
Qed.

Lemma F2_group_on : forall (X Y : Type) (P : X -> Y -> Prop) k1 k2 l1 l2, Forall2 P l1 l2 ->
  (forall x y, P x y -> k1 x = k2 y) -> Forall2 (Forall2 P) (group_on O k1 l1) (group_on O k2 l2).
Proof.
intros X Y P k1 k2 l1 l2 H K; rewrite !group_on_spec; unfold group_on_list.
apply (F2_map2 _ _ _ _ _ (fun p q => fst p = fst q /\ Forall2 P (snd p) (snd q))); [ | intros x y [_ Hxy]; exact Hxy].
apply (F2_fold_left _ _ _ _ _ P _ _ _ _ _ _ H); [constructor | ].
intros a1 a2 x1 x2 Ha Hx; rewrite (K _ _ Hx); apply F2_group_insert; assumption.
Qed.

(** ** Environments *)

Definition RSl (s' s : SqlFull.slice T relname) :=
  fst (fst s') =S= rs (fst (fst s)) /\ RL (snd (fst s')) (snd (fst s)) /\ snd s' = map re (snd s).

Definition REnv := Forall2 RSl.

Definition RCE (ce' ce : SqlFull.cte_env T relname) :=
  Forall2 (fun x' x => fst x' = fst x /\ fst (snd x') =S= rs (fst (snd x)) /\ RL (snd (snd x')) (snd (snd x))) ce' ce.

Lemma RCE_Rsort : forall ce' ce, RCE ce' ce -> Rsort ce' ce.
Proof. intros ce' ce H; unfold Rsort; induction H as [ | x' x ce' ce [E1 [E2 _]] H IH]; constructor; tauto. Qed.

Lemma RCE_find : forall ce' ce r, RCE ce' ce ->
  match Oset.find ORN r ce', Oset.find ORN r ce with
  | Some (_, l'), Some (_, l) => RL l' l
  | None, None => True
  | _, _ => False
  end.
Proof.
intros ce' ce r H; induction H as [ | [r' [s' l']] [r0 [s l]] ce' ce [E1 [E2 E3]] H IH]; [exact I | ].
simpl in E1, E2, E3; subst r'; cbn [Oset.find Mem.find fst].
unfold Oset.find in IH; destruct (Oset.eq_bool ORN r r0); [exact E3 | exact IH].
Qed.

Lemma RCE_cons : forall ce' ce r s' s l' l, RCE ce' ce -> s' =S= rs s -> RL l' l ->
  RCE ((r, (s', l')) :: ce') ((r, (s, l)) :: ce).
Proof. intros; constructor; [simpl; tauto | assumption]. Qed.

Lemma REnv_t : forall t' t env' env, RT t' t -> REnv env' env -> REnv (slice_t T relname t' :: env') (slice_t T relname t :: env).
Proof.
intros t' t env' env Ht H; constructor; [ | exact H].
split; [apply RT_labels; exact Ht | split; [constructor; [exact Ht | constructor] | reflexivity]].
Qed.

Lemma REnv_gs : forall sa' sa g' g hid env' env, sa' =S= rs sa -> RL g' g -> REnv env' env ->
  REnv (slice_gs sa' g' (map re hid) :: env') (slice_gs sa g hid :: env).
Proof.
intros sa' sa g' g hid env' env Hs Hg H; constructor; [ | exact H].
split; [ | split; [exact Hg | reflexivity]].
destruct Hg as [ | t' t g' g Ht _]; simpl; [exact Hs | apply RT_labels; exact Ht].
Qed.

Lemma lookup_R : forall env' env a, REnv env' env -> lookup env' (rho a) = lookup env a.
Proof.
intros env' env a H; induction H as [ | [[sa' g'] h'] [[sa g] h] env' env [S1 [S2 S3]] H IH]; simpl in *.
- apply null_of_rho.
- rewrite (Fset.mem_eq_2 _ _ _ S1), mem_rs; destruct (a inS? sa); [ | exact IH].
  destruct S2 as [ | t' t g' g Ht _]; [apply null_of_rho | apply RT_dot_all; exact Ht].
Qed.

Lemma is_hidden_R : forall env' env e, REnv env' env -> is_hidden env' (re e) = is_hidden env e.
Proof.
intros env' env e H; destruct H as [ | [[sa' g'] h'] [[sa g] h] env' env [_ [_ S3]] _]; [reflexivity | ].
simpl in S3; subst h'; unfold is_hidden; destruct h as [ | x h]; [reflexivity | ].
exact (existsb_eqb_re e (x :: h)).
Qed.

Lemma grouping_R : forall env' env x, REnv env' env ->
  match env' with (_, _, hid) :: _ => if existsb (sexpr_eqb (re x)) hid then 1%Z else 0%Z | nil => 0%Z end =
  match env with (_, _, hid) :: _ => if existsb (sexpr_eqb x) hid then 1%Z else 0%Z | nil => 0%Z end.
Proof.
intros env' env x H; destruct H as [ | [[sa' g'] h'] [[sa g] h] env' env [_ [_ S3]] _]; [reflexivity | ].
simpl in S3; subst h'; rewrite existsb_eqb_re; reflexivity.
Qed.

Lemma agg_env_rec_R : forall cols env' env, REnv env' env -> REnv (agg_env_rec (map rho cols) env') (agg_env_rec cols env).
Proof.
intros cols env' env H; induction H as [ | [[sa' g'] h'] [[sa g] h] env' env [S1 [S2 S3]] H IH]; [constructor | ].
simpl in *; rewrite (existsb_map_rho (fun a => a inS? sa)) by (intro a; rewrite (Fset.mem_eq_2 _ _ _ S1), mem_rs; reflexivity).
destruct (existsb _ cols); [constructor; [split; [exact S1 | split; assumption] | exact H] | exact IH].
Qed.

Lemma agg_env_R : forall cols env' env, REnv env' env -> REnv (agg_env (map rho cols) env') (agg_env cols env).
Proof.
intros cols env' env H; unfold agg_env; assert (K := agg_env_rec_R cols env' env H).
destruct K; [exact H | constructor; assumption].
Qed.



(** ** Expressions and conditions *)

Notation ev' := (eval_sexpr ORN O basesort' instance').
Notation ec' := (eval_scond ORN O basesort' instance').
Notation er' := (scond_raises ORN O basesort' instance').
Notation eq' := (eval_squery ORN O basesort' instance').
Notation es' := (eval_sspec ORN O basesort' instance').
Notation ef' := (eval_sfrom ORN O basesort' instance').
Notation ev := (eval_sexpr ORN O basesort instance).
Notation ec := (eval_scond ORN O basesort instance).
Notation er := (scond_raises ORN O basesort instance).
Notation eq_ := (eval_squery ORN O basesort instance).
Notation es := (eval_sspec ORN O basesort instance).
Notation ef := (eval_sfrom ORN O basesort instance).

(** rows with the environments in which they have been built *)
Definition RP (x' x : tuple T * SqlFull.senv T relname) := RT (fst x') (fst x) /\ REnv (snd x') (snd x).

Definition Ee (e : SqlFull.sexpr T relname) := forall ce' ce env' env, RCE ce' ce -> REnv env' env -> ev' ce' env' (re e) = ev ce env e.
Definition Ec (c : SqlFull.scond T relname) := forall ce' ce env' env, RCE ce' ce -> REnv env' env ->
  ec' ce' env' (rc c) = ec ce env c /\ er' ce' env' (rc c) = er ce env c.
Definition Eqr (q : SqlFull.squery T relname) := forall ce' ce env' env, RCE ce' ce -> REnv env' env ->
  RL (eq' ce' env' (rq q)) (eq_ ce env q).
Definition Es (sp : SqlFull.sspec T relname) := forall ce' ce env' env ex, RCE ce' ce -> REnv env' env ->
  Forall2 RP (es' ce' env' (rsp sp) (map re ex)) (es ce env sp ex).
Definition Ef (f : SqlFull.sfrom T relname) := forall ce' ce env' env, RCE ce' ce -> REnv env' env ->
  RL (ef' ce' env' (rf f)) (ef ce env f).

Lemma REnv_row : forall sa' sa t' t env' env, sa' =S= rs sa -> RT t' t -> REnv env' env ->
  REnv ((sa', t' :: nil, nil) :: env') ((sa, t :: nil, nil) :: env).
Proof.
intros sa' sa t' t env' env Hs Ht H; constructor; [ | exact H].
split; [exact Hs | split; [constructor; [exact Ht | constructor] | reflexivity]].
Qed.

Ltac unf :=
  cbn [r_e r_c r_q r_s r_f eval_sexpr eval_scond scond_raises eval_squery eval_sspec eval_sfrom] in *;
  fold ev' ec' er' eq' es' ef' ev ec er eq_ es ef in *; fold r_e r_c r_q r_s r_f in *.

Ltac open_e := unfold Ee, Ec, Eqr, Es, Ef, LE, LO; cbv beta.

Ltac prep :=
  repeat match goal with
         | H : (forall ce' ce env' env, _ -> _ -> _ /\ _) |- _ =>
           let H1 := fresh "IHc" in let H2 := fresh "IHr" in
           assert (H1 := fun ce' ce env' env a b => proj1 (H ce' ce env' env a b));
           assert (H2 := fun ce' ce env' env a b => proj2 (H ce' ce env' env a b)); clear H
         end.

Ltac renv := first [ assumption | apply REnv_t; [assumption | renv] | apply REnv_row; [assumption | assumption | renv] ].

Ltac leaf :=
  match goal with
  | H : forall ce' ce env' env, _ -> _ -> ?f ce' env' (?r ?x) = ?g ce env ?x |- ?f _ _ (?r ?x) = ?g _ _ ?x => apply H; [assumption | renv]
  | H : forall y, In y ?l -> forall ce' ce env' env, _ -> _ -> ?f ce' env' (?r y) = ?g ce env y, Hy : In ?x ?l
    |- ?f _ _ (?r ?x) = ?g _ _ ?x => apply (H x Hy); [assumption | renv]
  | H : forall e d n, In (O_By e d n) ?l -> forall ce' ce env' env, _ -> _ -> ?f ce' env' (?r e) = ?g ce env e,
    Hy : In (O_By ?x ?d ?n) ?l |- ?f _ _ (?r ?x) = ?g _ _ ?x => apply (H x d n Hy); [assumption | renv]
  | |- row_error O _ = row_error O _ => apply row_error_RT; assumption
  | |- lookup _ (rho ?a) = lookup _ ?a => apply lookup_R; renv
  | |- dot T _ (rho ?a) = dot T _ ?a => apply RT_dot_all; assumption
  end.

Ltac rl :=
  first [ eassumption
        | apply F2_filter; [rl | intros ? ? ?]
        | apply F2_sort_on; [rl | intros ? ? ?] ].

Ltac rcong :=
  repeat first
   [ reflexivity
   | leaf
   | match goal with |- existsb _ _ = existsb _ _ => apply (F2_existsb _ _ RT); [rl | intros ? ? ?] end
   | match goal with |- map _ (map r_e ?l) = map _ ?l => rewrite map_map; apply map_ext_in; intros ? ? end
   | match goal with |- map _ (map _ ?l) = map _ ?l => rewrite map_map; apply map_ext_in; intros [? ? ?] ? end
   | match goal with |- map _ _ = map _ _ => apply (F2_eq_map _ _ _ RT); [rl | intros ? ? ?] end
   | match goal with |- flat_map _ _ = flat_map _ _ => rewrite !flat_map_concat_map; f_equal end
   | match goal with |- ?L = ?R =>
       lazymatch L with context [match ?a with _ => _ end] =>
         lazymatch R with context [match ?b with _ => _ end] =>
           first [ constr_eq a b; destruct a
                 | let E := fresh "E" in assert (E : a = b) by rcong; rewrite E; destruct b ] end end end
   | f_equal ].

Ltac hid X :=
  match goal with He : REnv ?env' ?env |- _ =>
    let Hh := fresh "Hh" in
    assert (Hh := is_hidden_R env' env X He); unf; rewrite Hh; destruct (is_hidden env X); [reflexivity | ]; clear Hh
  end.

Lemma e_const : forall v, Ee (E_Const T relname v).
Proof. open_e; intros v ce' ce env' env Hc He; hid (E_Const T relname v); reflexivity. Qed.

Lemma e_col : forall a, Ee (E_Col T relname a).
Proof. open_e; intros a ce' ce env' env Hc He; hid (E_Col T relname a); rcong. Qed.

Lemma e_fun : forall f l, LE T relname Ee l -> Ee (E_Fun f l).
Proof. open_e; intros f l Hl ce' ce env' env Hc He; hid (E_Fun f l); rcong. Qed.

Lemma e_agg : forall ag sq e c, Ee e -> Ec c -> Ee (E_Agg ag sq e c).
Proof.
open_e; intros ag sq e c IHe IH ce' ce env' env Hc He; prep; hid (E_Agg ag sq e c).
rewrite (cols_e e ce' ce (RCE_Rsort _ _ Hc)), (cols_c c ce' ce (RCE_Rsort _ _ Hc)), <- map_app.
generalize (agg_env_R (sc_e ce e ++ scond_cols ORN basesort ce c) env' env He); intro K.
destruct K as [ | [[sa' g'] h'] [[sa g] h] X Y [S1 [S2 S3]] K]; [reflexivity | ]; simpl in S1, S2.
rcong.
Qed.

Lemma spec_re : forall lo : list (sorder T relname),
  map (@sorder_spec T relname) (map (fun o => match o with O_By e d n => O_By (re e) d n end) lo) = map (@sorder_spec T relname) lo.
Proof. intro lo; rewrite map_map; apply map_ext; intros [e d n]; reflexivity. Qed.

Lemma e_aggx : forall ag sq e sep lo c, Ee e -> (forall s, sep = Some s -> Ee s) -> LO T relname Ee lo -> Ec c ->
  Ee (E_AggX ag sq e sep lo c).
Proof.
open_e; intros ag sq e sep lo c IHe IHs IHo IH ce' ce env' env Hc He; prep; hid (E_AggX ag sq e sep lo c).
assert (R0 := RCE_Rsort _ _ Hc).
match goal with |- context [agg_env ?cols' env'] =>
  replace cols' with (map rho (sc_e ce e ++ scond_cols ORN basesort ce c ++
                (match sep with Some s => sc_e ce s | None => nil end) ++
                flat_map (fun o => match o with O_By e _ _ => sc_e ce e end) lo)) end.
2:{ rewrite !map_app, (cols_e e ce' ce R0), (cols_c c ce' ce R0), (Cflat_o lo ce' ce (fun x d n _ => cols_e x) R0).
    destruct sep as [s | ]; [rewrite (cols_e s ce' ce R0) | ]; reflexivity. }
match goal with |- context [agg_env (map rho ?cols) env'] => generalize (agg_env_R cols env' env He); intro K end.
destruct K as [ | [[sa' g'] h'] [[sa g] h] X Y [S1 [S2 S3]] K]; [reflexivity | ]; simpl in S1, S2.
destruct sep as [s | ]; [specialize (IHs s eq_refl) | clear IHs].
all: rewrite ?spec_re; rcong.

Qed.

Lemma e_case : forall c e1 e2, Ec c -> Ee e1 -> Ee e2 -> Ee (E_Case c e1 e2).
Proof. open_e; intros c e1 e2 IH IH1 IH2 ce' ce env' env Hc He; prep; hid (E_Case c e1 e2); rcong. Qed.

Lemma e_cond : forall c, Ec c -> Ee (E_Cond c).
Proof. open_e; intros c IH ce' ce env' env Hc He; prep; hid (E_Cond c); rcong. Qed.

Lemma e_sub : forall q, Eqr q -> Ee (E_Sub q).
Proof.
open_e; intros q IH ce' ce env' env Hc He; hid (E_Sub q).
generalize (IH ce' ce env' env Hc He); intro K.
rewrite (F2_existsb _ _ _ _ _ _ _ K row_error_RT); destruct (existsb (row_error O) (eq_ ce env q)); [reflexivity | ].
destruct K as [ | t' t l' l Ht K]; [reflexivity | ].
assert (V : match {{{labels T t'}}} with a :: nil => dot T t' a | _ => null O end =
            match {{{labels T t}}} with a :: nil => dot T t a | _ => null O end).
{ assert (L := elements_length _ _ (RT_labels _ _ Ht)).
  assert (M : forall a', In a' ({{{labels T t'}}}) -> In (rhoi a') ({{{labels T t}}})).
  { intros a' Ha; rewrite in_elements_iff in *; rewrite <- (Hrr' a'), (RT_mem _ _ _ Ht) in Ha; exact Ha. }
  destruct ({{{labels T t'}}}) as [ | a' [ | b' k']]; destruct ({{{labels T t}}}) as [ | a [ | b k]]; try discriminate L; trivial.
  destruct (M a' (or_introl eq_refl)) as [E | []]; rewrite (RT_dot' _ _ _ Ht), E; reflexivity. }
destruct K; rewrite V; reflexivity.
Qed.

Lemma e_grouping : forall x, Ee x -> Ee (E_Grouping x).
Proof.
open_e; intros x _ ce' ce env' env Hc He; hid (E_Grouping x).
f_equal; apply grouping_R; exact He.
Qed.

Lemma e_conj : forall a c1 c2, Ec c1 -> Ec c2 -> Ec (C_Conj a c1 c2).
Proof. open_e; intros a c1 c2 IH1 IH2 ce' ce env' env Hc He; prep; unf; split; rcong. Qed.

Lemma e_not : forall c, Ec c -> Ec (C_Not c).
Proof. open_e; intros c IH ce' ce env' env Hc He; prep; unf; split; rcong. Qed.

Lemma e_true : Ec (C_True T relname).
Proof. open_e; intros; split; reflexivity. Qed.

Lemma aff_re : forall l, map (sexpr_affinity O) (map re l) = map (sexpr_affinity O) l.
Proof. intro l; rewrite map_map; apply map_ext; intros [ | a | | | | | | | ]; simpl; trivial. Qed.

Lemma e_pred : forall p l, LE T relname Ee l -> Ec (C_Pred p l).
Proof.
open_e; intros p l IH ce' ce env' env Hc He; unf; rewrite aff_re.
assert (M : map (ev' ce' env') (map re l) = map (ev ce env) l) by rcong.
rewrite M; split; reflexivity.
Qed.

Lemma e_expr : forall e, Ee e -> Ec (C_Expr e).
Proof. open_e; intros e IH ce' ce env' env Hc He; unf; rewrite (IH ce' ce env' env Hc He); split; reflexivity. Qed.

Lemma dots_R : forall t' t la, RT t' t -> map (dot T t') (map rho la) = map (dot T t) la.
Proof. intros t' t la H; rewrite map_map; apply map_ext; intro a; apply RT_dot_all; exact H. Qed.

Lemma e_quant : forall qtf p l q la, LE T relname Ee l -> Eqr q -> Ec (C_Quant qtf p l q la).
Proof.
open_e; intros qtf p l q la IH IHq ce' ce env' env Hc He; unf; cbv zeta.
assert (M : map (ev' ce' env') (map re l) = map (ev ce env) l) by rcong.
assert (K := IHq ce' ce env' env Hc He); rewrite M; split.
- apply (F2_quant _ _ RT); [exact K | intros x y Hxy; rewrite (dots_R _ _ _ Hxy); reflexivity].
- rewrite (F2_existsb _ _ _ _ _ _ _ K row_error_RT); f_equal.
  apply (F2_existsb _ _ RT); [exact K | intros x y Hxy; rewrite (dots_R _ _ _ Hxy); reflexivity].
Qed.

Lemma e_in : forall l q la, LE T relname Ee l -> Eqr q -> Ec (C_In l q la).
Proof.
open_e; intros l q la IH IHq ce' ce env' env Hc He; unf; cbv zeta.
assert (M : map (ev' ce' env') (map re l) = map (ev ce env) l) by rcong.
assert (K := IHq ce' ce env' env Hc He); rewrite M; split.
- apply (F2_quant _ _ RT); [exact K | intros x y Hxy; rewrite (dots_R _ _ _ Hxy); reflexivity].
- rewrite (F2_existsb _ _ _ _ _ _ _ K row_error_RT); reflexivity.
Qed.

Lemma e_exists : forall q, Eqr q -> Ec (C_Exists q).
Proof.
open_e; intros q IHq ce' ce env' env Hc He; unf.
assert (K := IHq ce' ce env' env Hc He); split; [destruct K; reflexivity | apply (F2_existsb _ _ RT); [exact K | apply row_error_RT]].
Qed.

(** ** Queries *)

Lemma RS_equal : forall s1' s1 s2' s2, s1' =S= rs s1 -> s2' =S= rs s2 -> Fset.equal (A T) s1' s2' = Fset.equal (A T) s1 s2.
Proof.
intros s1' s1 s2' s2 H1 H2; apply eq_true_iff_eq; rewrite !Fset.equal_spec; split; intros H a.
- rewrite <- (mem_rs s1), <- (mem_rs s2), <- (Fset.mem_eq_2 _ _ _ H1), <- (Fset.mem_eq_2 _ _ _ H2); apply H.
- rewrite (Fset.mem_eq_2 _ _ _ H1), (Fset.mem_eq_2 _ _ _ H2), !mem_rs'; apply H.
Qed.

Lemma q_table : forall r, Eqr (SQ_Table T r).
Proof.
open_e; intros r ce' ce env' env Hc He; unf.
generalize (RCE_find ce' ce r Hc); destruct (Oset.find ORN r ce') as [[s' l'] | ]; destruct (Oset.find ORN r ce) as [[s l] | ];
  intro K; try contradiction; [exact K | apply Hinst].
Qed.

Lemma q_set : forall o sq q1 q2, Eqr q1 -> Eqr q2 -> Eqr (SQ_Set o sq q1 q2).
Proof.
open_e; intros o sq q1 q2 IH1 IH2 ce' ce env' env Hc He; unf.
assert (R0 := RCE_Rsort _ _ Hc).
rewrite (RS_equal _ _ _ _ (sort_rename q1 ce' ce R0) (sort_rename q2 ce' ce R0)).
destruct (Fset.equal (A T) (sq_sort ce q1) (sq_sort ce q2)); [ | constructor].
assert (K1 := IH1 ce' ce env' env Hc He); assert (K2 := IH2 ce' ce env' env Hc He).
apply unify_rows_R; [apply sort_rename; exact R0 | ]; apply keep_errors_R; [apply set_op_R; assumption | apply RL_app; assumption].
Qed.

Lemma RP_fst : forall l' l, Forall2 RP l' l -> RL (map (@fst _ _) l') (map (@fst _ _) l).
Proof. intros l' l H; apply (F2_map2 _ _ _ _ _ RP); [exact H | intros x y [Hxy _]; exact Hxy]. Qed.

Lemma q_select : forall sp, Es sp -> Eqr (SQ_Select sp).
Proof. open_e; intros sp IH ce' ce env' env Hc He; unf; apply RP_fst; exact (IH ce' ce env' env nil Hc He). Qed.

(** *** ORDER BY and FETCH *)

Notation ordr' := (ord_rows T relname ORN basesort' instance' O).
Notation ordk' := (ord_keys T relname ORN basesort' instance' O).
Notation ordr := (ord_rows T relname ORN basesort instance O).
Notation ordk := (ord_keys T relname ORN basesort instance O).
Notation rlo lo := (map (fun o : sorder T relname => match o with O_By e d n => O_By (re e) d n end) lo).

Lemma output_col_R : forall t' t e, RT t' t -> is_output_col t' (re e) = is_output_col t e.
Proof.
intros t' t e H; destruct e; simpl; trivial.
rewrite (RT_mem _ _ _ H), (RT_dot_all _ _ _ H); reflexivity.
Qed.

Lemma ordk_R : forall lo ce' ce x' x, LO T relname Ee lo -> RCE ce' ce -> RP x' x -> ordk' ce' (rlo lo) x' = ordk ce lo x.
Proof.
intros lo ce' ce x' x Ho Hc [H1 H2]; unfold ord_keys; rewrite map_map; apply map_ext_in; intros [e d n] Hin.
rewrite (output_col_R _ _ e H1); destruct (is_output_col (fst x) e); [reflexivity | apply (Ho e d n Hin); assumption].
Qed.

Lemma ordr_R : forall q lo ce' ce env' env, RCE ce' ce -> REnv env' env -> Eqr q -> (forall sp, q = SQ_Select sp -> Es sp) ->
  Forall2 RP (ordr' ce' env' (rq q) (rlo lo)) (ordr ce env q lo).
Proof.
intros q lo ce' ce env' env Hc He Hq Hs.
assert (M : Forall2 RP (map (fun t => (t, slice_t T relname t :: env')) (eq' ce' env' (rq q)))
                       (map (fun t => (t, slice_t T relname t :: env)) (eq_ ce env q))).
{ apply (F2_map2 _ _ _ _ _ RT); [apply Hq; assumption | intros x y Hxy; split; [exact Hxy | apply REnv_t; assumption]]. }
unfold ord_rows; destruct q; try exact M.
cbn [r_q]; fold r_s.
replace (map (fun o : sorder T relname => match o with O_By e _ _ => e end) (rlo lo))
  with (map re (map (fun o : sorder T relname => match o with O_By e _ _ => e end) lo))
  by (rewrite !map_map; apply map_ext; intros [e d n]; reflexivity).
apply (Hs s eq_refl); assumption.
Qed.

Lemma flag_R : forall (k1 k2 : tuple T * SqlFull.senv T relname -> list (value T)) l' l,
  (forall x' x, RP x' x -> k1 x' = k2 x) -> Forall2 RP l' l ->
  Forall2 RP (flag_rows T relname O k1 l') (flag_rows T relname O k2 l).
Proof.
intros k1 k2 l' l K H; unfold flag_rows; apply (F2_map2 _ _ _ _ _ _ _ _ _ _ H).
intros x y Hxy; rewrite (K x y Hxy); destruct (existsb _ _); [ | exact Hxy].
destruct Hxy as [H1 H2]; split; [apply err_row_RT; exact H1 | exact H2].
Qed.

Lemma q_order : forall q lo off lim, Eqr q -> (forall sp, q = SQ_Select sp -> Es sp) -> LO T relname Ee lo -> Eqr (SQ_Order q lo off lim).
Proof.
intros q lo off lim Hq Hs Ho ce' ce env' env Hc He; cbn [r_q]; fold r_q r_e.
rewrite !eval_order; cbv zeta.
assert (K := flag_R _ _ _ _ (fun x' x => ordk_R lo ce' ce x' x Ho Hc) (ordr_R q lo ce' ce env' env Hc He Hq Hs)).
apply keep_errors_R; apply RP_fst; [ | exact K].
rewrite spec_re; apply F2_offset_limit, F2_sort_on; [exact K | intros x y Hxy; apply ordk_R; assumption].
Qed.

Lemma F2_take : forall (X Y : Type) (P : X -> Y -> Prop) (c1 : X -> comparison) (c2 : Y -> comparison) l1 l2, Forall2 P l1 l2 ->
  (forall x y, P x y -> c1 x = c2 y) ->
  Forall2 P ((fix take (l : list X) : list X :=
               match l with x :: l' => match c1 x with Datatypes.Eq => x :: take l' | _ => nil end | nil => nil end) l1)
            ((fix take (l : list Y) : list Y :=
               match l with x :: l' => match c2 x with Datatypes.Eq => x :: take l' | _ => nil end | nil => nil end) l2).
Proof.
intros X Y P c1 c2 l1 l2 H K; induction H as [ | x y l1 l2 Hxy H IH]; [constructor | ].
rewrite (K x y Hxy); destruct (c2 y); try constructor; trivial.
Qed.

Lemma fetch_R : forall lo off ties pct n (k1 k2 : tuple T * SqlFull.senv T relname -> list (value T)) l1 l2, Forall2 RP l1 l2 ->
  (forall x y, RP x y -> k1 x = k2 y) ->
  RL (fetch_rest T relname O (rlo lo) off ties pct n k1 l1) (fetch_rest T relname O lo off ties pct n k2 l2).
Proof.
intros lo off ties pct n k1 k2 l1 l2 H K; unfold fetch_rest; cbv zeta; rewrite spec_re.
assert (S := F2_sort_on _ O _ _ _ (map (@sorder_spec T relname) lo) k1 k2 l1 l2 H K).
assert (L := F2_length _ _ _ _ _ S).
assert (Af : Forall2 RP (match off with Some k => skipn (N.to_nat k) (sort_on O (map (@sorder_spec T relname) lo) k1 l1)
                         | None => sort_on O (map (@sorder_spec T relname) lo) k1 l1 end)
                        (match off with Some k => skipn (N.to_nat k) (sort_on O (map (@sorder_spec T relname) lo) k2 l2)
                         | None => sort_on O (map (@sorder_spec T relname) lo) k2 l2 end))
  by (destruct off; [apply F2_skipn | ]; exact S).
rewrite L.
match goal with |- RL (keep_errors O (map _ (?F1 ++ ?E1)) _) (keep_errors O (map _ (?F2 ++ ?E2)) _) =>
  assert (Fi : Forall2 RP F1 F2) by (apply F2_firstn; exact Af);
  assert (Ex : Forall2 RP E1 E2) end.
- destruct ties; [ | constructor].
  assert (Rv := F2_rev' _ _ _ _ _ Fi); destruct Rv as [ | x y r1 r2 Hxy _]; [constructor | ].
  apply F2_take; [apply F2_skipn; exact Af | ].
  intros a b Hab; rewrite (K x y Hxy), (K a b Hab); reflexivity.
- apply keep_errors_R; apply RP_fst; [apply F2_app; assumption | exact H].
Qed.

Lemma q_fetch : forall q lo off ties pct n, Eqr q -> (forall sp, q = SQ_Select sp -> Es sp) -> LO T relname Ee lo ->
  Eqr (SQ_Fetch q lo off ties pct n).
Proof.
intros q lo off ties pct n Hq Hs Ho ce' ce env' env Hc He; cbn [r_q]; fold r_q r_e.
rewrite !eval_fetch; apply fetch_R; [ | intros x y Hxy; apply ordk_R; assumption].
exact (flag_R _ _ _ _ (fun x' x => ordk_R lo ce' ce x' x Ho Hc) (ordr_R q lo ce' ce env' env Hc He Hq Hs)).
Qed.

(** *** Windows *)

Fixpoint r_wf (f : swfun T relname) : swfun T relname :=
  match f with
  | W_Agg ag sq e fr => W_Agg ag sq (r_e e) fr
  | W_Lag e n d => W_Lag (r_e e) n (r_e d)
  | W_Lead e n d => W_Lead (r_e e) n (r_e d)
  | W_First_Value e fr => W_First_Value (r_e e) fr
  | W_Last_Value e fr => W_Last_Value (r_e e) fr
  | W_Nth_Value e n fr => W_Nth_Value (r_e e) n fr
  | W_Opts f' ign last => W_Opts (r_wf f') ign last
  | f => f
  end.

Lemma F2_nth_error : forall (X Y : Type) (P : X -> Y -> Prop) l1 l2, Forall2 P l1 l2 -> forall j,
  match nth_error l1 j, nth_error l2 j with Some x, Some y => P x y | None, None => True | _, _ => False end.
Proof.
intros X Y P l1 l2 H; induction H as [ | x y l1 l2 Hxy H IH]; intros [ | j]; simpl; trivial; apply IH.
Qed.

Lemma frame_rows_R : forall fr s' s gidx rk i, RL s' s -> RL (frame_rows T fr s' gidx rk i) (frame_rows T fr s gidx rk i).
Proof.
intros fr s' s gidx rk i H; unfold frame_rows; rewrite (F2_length _ _ _ _ _ H).
induction (frame_positions fr (length s) gidx rk i) as [ | j l IH]; [constructor | ]; simpl.
apply RL_app; [ | exact IH].
generalize (F2_nth_error _ _ _ _ _ H j); destruct (nth_error s' j); destruct (nth_error s j); intro K; try contradiction;
  constructor; [exact K | constructor].
Qed.

Section WSem.

Variables arg' arg : tuple T -> value T.
Variable a : attribute T.
Hypothesis Harg : forall t' t, RT t' t -> arg' t' = arg t.

Lemma head_R : forall l' l, RL l' l ->
  match l' with t' :: _ => arg' t' | nil => null_of T (rho a) end = match l with t :: _ => arg t | nil => null_of T a end.
Proof. intros l' l H; destruct H; [apply null_of_rho | apply Harg; assumption]. Qed.

Lemma nth_R : forall l' l n, RL l' l ->
  match nth_error l' n with Some t' => arg' t' | None => null_of T (rho a) end =
  match nth_error l n with Some t => arg t | None => null_of T a end.
Proof.
intros l' l n H; generalize (F2_nth_error _ _ _ _ _ H n); destruct (nth_error l' n); destruct (nth_error l n); intro K;
  try contradiction; [apply Harg; exact K | apply null_of_rho].
Qed.

Lemma nth_d_R : forall (d' d : tuple T -> value T) t' t l' l n, RL l' l -> d' t' = d t ->
  match nth_error l' n with Some x => arg' x | None => d' t' end = match nth_error l n with Some x => arg x | None => d t end.
Proof.
intros d' d t' t l' l n H E; generalize (F2_nth_error _ _ _ _ _ H n); destruct (nth_error l' n); destruct (nth_error l n); intro K;
  try contradiction; [apply Harg; exact K | exact E].
Qed.

Lemma keep_R : forall (ign : bool) l' l, RL l' l ->
  RL (if ign then filter (fun t' => negb (is_null O (arg' t'))) l' else l') (if ign then filter (fun t' => negb (is_null O (arg t'))) l else l).
Proof. intros ign l' l H; destruct ign; [ | exact H]; apply F2_filter; [exact H | intros x y Hxy; rewrite (Harg _ _ Hxy); reflexivity]. Qed.

End WSem.

Lemma wsem_R : forall f (ev1 ev2 : SqlFull.sexpr T relname -> tuple T -> value T),
  (forall e, In e (wexprs T relname f) -> forall t' t, RT t' t -> ev1 (re e) t' = ev2 e t) ->
  forall a s' s gidx rk i t' t, RL s' s -> RT t' t ->
  eval_wsem O (rho a) (wcomp T relname ev1 (r_wf f)) s' gidx rk i t' = eval_wsem O a (wcomp T relname ev2 f) s gidx rk i t.
Proof.
intros f ev1 ev2; induction f as [ag sq e fr | | | | k | | | e k d | e k d | e fr | e fr | e k fr | f IHf ign last];
  intros He att s' s gidx rk i t' t Hs Ht; cbn [r_wf wcomp eval_wsem wexprs] in *;
  rewrite ?(F2_length _ _ _ _ _ Hs); try reflexivity.
- rewrite (F2_eq_map _ _ _ RT (ev1 (re e)) (ev2 e) _ _ (frame_rows_R fr s' s gidx rk i Hs)); [reflexivity | ].
  intros; apply He; [left; reflexivity | assumption].
- destruct k; [apply null_of_rho | reflexivity].
- cbv zeta; destruct (if Nat.leb k i then Some (i - k) else None) as [j | ].
  + apply nth_d_R; [intros; apply He; [left; reflexivity | assumption] | exact Hs | apply He; [right; left; reflexivity | exact Ht]].
  + apply He; [right; left; reflexivity | exact Ht].
- cbv zeta; apply nth_d_R; [intros; apply He; [left; reflexivity | assumption] | exact Hs | apply He; [right; left; reflexivity | exact Ht]].
- apply head_R; [intros; apply He; [left; reflexivity | assumption] | apply frame_rows_R; exact Hs].
- apply head_R; [intros; apply He; [left; reflexivity | assumption] | apply F2_rev', frame_rows_R; exact Hs].
- destruct k; [apply null_of_rho | ].
  apply nth_R; [intros; apply He; [left; reflexivity | assumption] | apply frame_rows_R; exact Hs].
- destruct f as [ag sq e fr | | | | k | | | e k d | e k d | e fr | e fr | e k fr | f ign0 last0];
    cbn [r_wf wcomp wexprs] in *; try (apply IHf; assumption).
  + assert (Ha : forall t' t, RT t' t -> ev1 (re e) t' = ev2 e t) by (intros; apply He; [left; reflexivity | assumption]).
    destruct k; [apply He; [left; reflexivity | exact Ht] | ]; cbv zeta.
    apply nth_d_R; [exact Ha | | apply He; [right; left; reflexivity | exact Ht]].
    apply keep_R; [exact Ha | apply F2_rev', F2_firstn; exact Hs].
  + assert (Ha : forall t' t, RT t' t -> ev1 (re e) t' = ev2 e t) by (intros; apply He; [left; reflexivity | assumption]).
    destruct k; [apply He; [left; reflexivity | exact Ht] | ]; cbv zeta.
    apply nth_d_R; [exact Ha | | apply He; [right; left; reflexivity | exact Ht]].
    apply keep_R; [exact Ha | apply F2_skipn; exact Hs].
  + assert (Ha : forall t' t, RT t' t -> ev1 (re e) t' = ev2 e t) by (intros; apply He; [left; reflexivity | assumption]).
    cbv zeta; apply head_R; [exact Ha | ]; apply keep_R; [exact Ha | ].
    destruct last; [apply F2_rev' | ]; apply frame_rows_R; exact Hs.
  + assert (Ha : forall t' t, RT t' t -> ev1 (re e) t' = ev2 e t) by (intros; apply He; [left; reflexivity | assumption]).
    cbv zeta; apply head_R; [exact Ha | ]; apply keep_R; [exact Ha | ].
    destruct last; [ | apply F2_rev']; apply frame_rows_R; exact Hs.
  + assert (Ha : forall t' t, RT t' t -> ev1 (re e) t' = ev2 e t) by (intros; apply He; [left; reflexivity | assumption]).
    destruct k; [apply null_of_rho | ]; cbv zeta.
    apply nth_R; [exact Ha | ]; apply keep_R; [exact Ha | ].
    destruct last; [apply F2_rev' | ]; apply frame_rows_R; exact Hs.
Qed.

Lemma extend_RT : forall t' t a v, RT t' t -> RT (extend_tuple O t' (rho a) v) (extend_tuple O t a v).
Proof.
intros t' t a v H; unfold extend_tuple; apply RT_mk_tuple.
- apply RS_union; [apply RT_labels; exact H | ].
  rewrite Fset.equal_spec; intro b; rewrite (Fset.mem_eq_2 _ _ _ (rs_singleton a)); reflexivity.
- intros x _; rewrite rho_eqb, store_rho, (RT_dot_all _ _ _ H); reflexivity.
Qed.

Lemma F2_indexed_rec : forall (X Y : Type) (P : X -> Y -> Prop) l1 l2 i, Forall2 P l1 l2 ->
  Forall2 (fun p q => fst p = fst q /\ P (snd p) (snd q)) (indexed_rec i l1) (indexed_rec i l2).
Proof. intros X Y P l1 l2 i H; revert i; induction H; intro i; simpl; constructor; [split; trivial | apply IHForall2]. Qed.

Lemma eval_window_R : forall (part' part keys' keys : tuple T -> list (value T)) specs a w' w rows' rows,
  (forall t' t, RT t' t -> part' t' = part t) -> (forall t' t, RT t' t -> keys' t' = keys t) ->
  (forall s' s gidx rk i t' t, RL s' s -> RT t' t -> eval_wsem O (rho a) w' s' gidx rk i t' = eval_wsem O a w s gidx rk i t) ->
  RL rows' rows -> RL (eval_window O part' specs keys' (rho a) w' rows') (eval_window O part specs keys a w rows).
Proof.
intros part' part keys' keys specs a w' w rows' rows Hp Hk Hw H; unfold eval_window.
apply (F2_flat_map _ _ _ _ RL); [apply F2_group_on; assumption | ].
intros g' g Hg; cbv zeta.
assert (S := F2_sort_on _ O _ _ _ specs keys' keys g' g Hg Hk).
rewrite (F2_eq_map _ _ _ _ keys' keys _ _ S Hk).
apply (F2_map2 _ _ _ _ _ _ _ _ _ _ (F2_indexed_rec _ _ _ _ _ 0 S)).
intros [i t'] [j t] [E Ht]; simpl in E, Ht; subst j; simpl.
rewrite (Hw _ _ _ _ _ _ _ S Ht); apply extend_RT; exact Ht.
Qed.

Notation wfun' := (wfun T relname ORN basesort' instance' O).
Notation wfun_ := (wfun T relname ORN basesort instance O).

Lemma wfun_R : forall f lp lo a ce' ce env' env rows' rows, RCE ce' ce -> REnv env' env ->
  LE T relname Ee lp -> LO T relname Ee lo -> LE T relname Ee (wexprs T relname f) -> RL rows' rows ->
  RL (wfun' ce' env' (W_As (r_wf f) (map re lp) (rlo lo) (rho a)) rows') (wfun_ ce env (W_As f lp lo a) rows).
Proof.
intros f lp lo a ce' ce env' env rows' rows Hc He Hp Ho Hf H; unfold wfun; cbv zeta; rewrite spec_re.
assert (Kp : forall t' t, RT t' t -> map (fun e => ev' ce' (slice_t T relname t' :: env') e) (map re lp) =
                                     map (fun e => ev ce (slice_t T relname t :: env) e) lp).
{ intros t' t Ht; rewrite map_map; apply map_ext_in; intros e Ie; apply (Hp e Ie); [exact Hc | apply REnv_t; assumption]. }
assert (Kk : forall t' t, RT t' t ->
    map (fun o : sorder T relname => match o with O_By e _ _ => ev' ce' (slice_t T relname t' :: env') e end) (rlo lo) =
    map (fun o : sorder T relname => match o with O_By e _ _ => ev ce (slice_t T relname t :: env) e end) lo).
{ intros t' t Ht; rewrite map_map; apply map_ext_in; intros [e d n] Ie; apply (Ho e d n Ie); [exact Hc | apply REnv_t; assumption]. }
apply eval_window_R; trivial.
- intros; apply wsem_R; trivial.
  intros e Ie x' x Hx; apply (Hf e Ie); [exact Hc | apply REnv_t; assumption].
- apply (F2_map2 _ _ _ _ _ _ _ _ _ _ H); intros t' t Ht; rewrite (Kp _ _ Ht), (Kk _ _ Ht).
  destruct (existsb _ _); [apply err_row_RT | ]; exact Ht.
Qed.

Lemma q_window : forall q lw, Eqr q ->
  (forall f lp lo a, In (W_As f lp lo a) lw -> LE T relname Ee lp /\ LO T relname Ee lo /\ LE T relname Ee (wexprs T relname f)) ->
  Eqr (SQ_Window q lw).
Proof.
intros q lw Hq Hw ce' ce env' env Hc He; cbn [r_q]; fold r_q r_e.
rewrite !eval_windows.
apply (F2_fold_left _ _ _ _ RL (fun w' w => forall r' r, RL r' r -> RL (w' r') (w r))); [ | apply Hq; assumption | intros; auto].
rewrite map_map; apply F2_map; intros [f lp lo a] Hin r' r Hr.
destruct (Hw f lp lo a Hin) as [Hp [Ho Hf]].
exact (wfun_R f lp lo a ce' ce env' env r' r Hc He Hp Ho Hf Hr).
Qed.

(** *** WITH *)

Lemma q_with : forall r q1 q2, Eqr q1 -> Eqr q2 -> Eqr (SQ_With r q1 q2).
Proof.
open_e; intros r q1 q2 IH1 IH2 ce' ce env' env Hc He; unf.
apply IH2; [ | exact He].
apply RCE_cons; [exact Hc | apply sort_rename, RCE_Rsort; exact Hc | apply IH1; assumption].
Qed.

Lemma rec_loop_R : forall (step' step : list (tuple T) -> list (tuple T)) d sa' sa,
  (forall w' w, RL w' w -> RL (step' w') (step w)) -> sa' =S= rs sa ->
  forall n acc' acc work' work, RL acc' acc -> RL work' work ->
  RL (rec_loop O step' d sa' n acc' work') (rec_loop O step d sa n acc work).
Proof.
intros step' step d sa' sa Hstep Hs n; induction n as [ | n IH]; intros acc' acc work' work Ha Hw; simpl.
- destruct Hw; [exact Ha | ].
  apply RL_app; [exact Ha | constructor; [apply err_row_RT, null_tuple_RT; exact Hs | constructor]].
- destruct Hw as [ | x' x w' w Hx Hw]; [exact Ha | ].
  assert (K : RL (x' :: w') (x :: w)) by (constructor; assumption).
  assert (N : RL (if d then eval_set_op O Diff Set_Distinct (step' (x' :: w')) acc' else step' (x' :: w'))
                 (if d then eval_set_op O Diff Set_Distinct (step (x :: w)) acc else step (x :: w)))
    by (destruct d; [apply set_op_R; [apply Hstep; exact K | exact Ha] | apply Hstep; exact K]).
  apply IH; [apply RL_app; assumption | exact N].
Qed.

Lemma q_withrec : forall sq r q1 q2 q3, Eqr q1 -> Eqr q2 -> Eqr q3 -> Eqr (SQ_WithRec sq r q1 q2 q3).
Proof.
open_e; intros sq r q1 q2 q3 IH1 IH2 IH3 ce' ce env' env Hc He; unf; cbv zeta.
assert (R0 := RCE_Rsort _ _ Hc); assert (S1 := sort_rename q1 ce' ce R0).
assert (B : RL (if is_distinct sq then eval_set_op O Union Set_Distinct (eq' ce' env' (rq q1)) nil else eq' ce' env' (rq q1))
               (if is_distinct sq then eval_set_op O Union Set_Distinct (eq_ ce env q1) nil else eq_ ce env q1)).
{ destruct (is_distinct sq); [apply set_op_R; [apply IH1; assumption | constructor] | apply IH1; assumption]. }
apply IH3; [ | exact He].
apply RCE_cons; [exact Hc | exact S1 | ].
apply rec_loop_R; trivial.
intros w' w Hw; apply IH2; [apply RCE_cons; assumption | exact He].
Qed.

(** ** FROM *)

Lemma rename_RT : forall r t' t, RT t' t -> RT (SqlFull.rename_tuple O (r_ren r) t') (SqlFull.rename_tuple O r t).
Proof.
intros [ | l] t' t H; [exact H | ]; unfold SqlFull.rename_tuple, r_ren; apply RT_mk_tuple.
- rewrite Fset.equal_spec; intro b; rewrite (Fset.mem_eq_2 _ _ _ (rs_mk_set _)), !map_map; reflexivity.
- intros b _; induction l as [ | [x y] l IH]; simpl; [apply null_of_rho | ].
  rewrite rho_eqb; destruct (Oset.eq_bool (OAtt T) b y); [rewrite store_rho, (RT_dot_all _ _ _ H); reflexivity | exact IH].
Qed.

Lemma fr_query : forall q r, Eqr q -> Ef (Fr_Query q r).
Proof.
open_e; intros q r IH ce' ce env' env Hc He; unf.
apply (F2_map2 _ _ _ _ _ RT); [apply IH; assumption | ].
intros t' t Ht; cbv zeta; assert (K := rename_RT r _ _ Ht).
rewrite (row_error_RT _ _ Ht), (row_error_RT _ _ K); destruct (_ && _); [apply err_row_RT | ]; exact K.
Qed.

Lemma nil_or_R : forall l' l x' x, RL l' l -> RL x' x ->
  RL (match l' with nil => x' | t :: l0 => t :: l0 end) (match l with nil => x | t :: l0 => t :: l0 end).
Proof. intros l' l x' x H K; destruct H; [exact K | constructor; assumption]. Qed.

Lemma join_R : forall jt s1' s1 s2' s2 l1' l1 (right' right : tuple T -> list (tuple T)) l2' l2 (on' on : tuple T -> bool)
  (mark' mark : tuple T -> tuple T),
  s1' =S= rs s1 -> s2' =S= rs s2 -> RL l1' l1 -> (forall t' t, RT t' t -> RL (right' t') (right t)) -> RL l2' l2 ->
  (forall t' t, RT t' t -> on' t' = on t) -> (forall t' t, RT t' t -> RT (mark' t') (mark t)) ->
  RL (eval_join T jt s1' s2' l1' right' l2' on' mark') (eval_join T jt s1 s2 l1 right l2 on mark).
Proof.
intros jt s1' s1 s2' s2 l1' l1 right' right l2' l2 on' on mark' mark S1 S2 H1 Hr H2 Hon Hm; unfold eval_join; cbv zeta.
assert (M : forall t' t, RT t' t -> RL (map mark' (filter on' (map (join_tuple T t') (right' t'))))
                                       (map mark (filter on (map (join_tuple T t) (right t))))).
{ intros t' t Ht; apply (F2_map2 _ _ _ _ _ RT); [ | exact Hm]; apply F2_filter; [ | exact Hon].
  apply (F2_map2 _ _ _ _ _ RT); [apply Hr; exact Ht | intros; apply RT_join; assumption]. }
assert (I : RL (flat_map (fun t1 => map mark' (filter on' (map (join_tuple T t1) (right' t1)))) l1')
               (flat_map (fun t1 => map mark (filter on (map (join_tuple T t1) (right t1)))) l1))
  by (apply (F2_flat_map _ _ _ _ RT); assumption).
assert (L : RL (flat_map (fun t1 => match map mark' (filter on' (map (join_tuple T t1) (right' t1))) with
                                    | nil => join_tuple T t1 (null_tuple T s2') :: nil | l => l end) l1')
               (flat_map (fun t1 => match map mark (filter on (map (join_tuple T t1) (right t1))) with
                                    | nil => join_tuple T t1 (null_tuple T s2) :: nil | l => l end) l1)).
{ apply (F2_flat_map _ _ _ _ RT); [exact H1 | intros t' t Ht].
  apply nil_or_R; [apply M; exact Ht | constructor; [apply RT_join; [exact Ht | apply null_tuple_RT; exact S2] | constructor]]. }
assert (P : RL (map (fun t2 => join_tuple T (null_tuple T s1') t2)
                    (filter (fun t2 => negb (existsb (fun t1 => on' (join_tuple T t1 t2)) l1')) l2'))
               (map (fun t2 => join_tuple T (null_tuple T s1) t2)
                    (filter (fun t2 => negb (existsb (fun t1 => on (join_tuple T t1 t2)) l1)) l2))).
{ apply (F2_map2 _ _ _ _ _ RT); [ | intros; apply RT_join; [apply null_tuple_RT; exact S1 | assumption]].
  apply F2_filter; [exact H2 | intros x y Hxy; f_equal].
  apply (F2_existsb _ _ RT); [exact H1 | intros a b Hab; apply Hon, RT_join; assumption]. }
destruct jt; trivial; apply RL_app; assumption.
Qed.

Lemma fr_join : forall jt lat f1 f2 c, Ef f1 -> Ef f2 -> Ec c -> Ef (Fr_Join jt lat f1 f2 c).
Proof.
open_e; intros jt lat f1 f2 c IH1 IH2 IH ce' ce env' env Hc He; prep; unf; cbv zeta.
assert (R0 := RCE_Rsort _ _ Hc).
assert (K1 := IH1 ce' ce env' env Hc He); assert (K2 := IH2 ce' ce env' env Hc He).
assert (E : lat || existsb (row_error O) (ef' ce' env' (rf f1) ++ ef' ce' env' (rf f2)) =
            lat || existsb (row_error O) (ef ce env f1 ++ ef ce env f2))
  by (f_equal; apply (F2_existsb _ _ RT); [apply RL_app; assumption | apply row_error_RT]).
rewrite E.
match goal with |- RL (if ?b then keep_errors O ?j' _ else _) (if _ then keep_errors O ?j _ else _) => assert (J : RL j' j) end.
- apply join_R; trivial; try (apply sort_rename_f; exact R0).
  + intros t' t Ht; destruct lat; [apply IH2; [exact Hc | apply REnv_t; assumption] | exact K2].
  + intros t' t Ht; rewrite (row_error_RT _ _ Ht), (IHr ce' ce _ _ Hc (REnv_t _ _ _ _ Ht He)), (IHc ce' ce _ _ Hc (REnv_t _ _ _ _ Ht He)).
    reflexivity.
  + intros t' t Ht; rewrite (IHr ce' ce _ _ Hc (REnv_t _ _ _ _ Ht He)); destruct (er _ _ _); [apply err_row_RT | ]; exact Ht.
- clear E; remember (lat || existsb (row_error O) (ef ce env f1 ++ ef ce env f2)) as b; destruct b;
    [apply keep_errors_R; [exact J | apply RL_app; assumption] | exact J].
Qed.

Lemma frow_RT : forall atts l,
  RT (mk_tuple T (Fset.mk_set (A T) (map rho atts))
        (fun a => match find (fun p : attribute T * value T => Oset.eq_bool (OAtt T) (fst p) a) (combine (map rho atts) l) with
                  | Some (_, v) => v | None => null_of T a end))
     (mk_tuple T (Fset.mk_set (A T) atts)
        (fun a => match find (fun p : attribute T * value T => Oset.eq_bool (OAtt T) (fst p) a) (combine atts l) with
                  | Some (_, v) => v | None => null_of T a end)).
Proof.
intros atts l; apply RT_mk_tuple.
- rewrite Fset.equal_spec; intro b; rewrite (Fset.mem_eq_2 _ _ _ (rs_mk_set _)); reflexivity.
- intros a _; revert l; induction atts as [ | b atts IH]; intros [ | v l]; simpl; try apply null_of_rho.
  rewrite rho_eqb; destruct (Oset.eq_bool (OAtt T) b a); [reflexivity | apply IH].
Qed.

Lemma fr_fun : forall name args ord atts, LE T relname Ee args -> Ef (Fr_Fun name args ord atts).
Proof.
open_e; intros name args ord atts IH ce' ce env' env Hc He; unf; cbv zeta.
assert (M : map (ev' ce' env') (map re args) = map (ev ce env) args) by rcong.
assert (C : forall v : value T, map (fun _ : attribute T => v) (map rho atts) = map (fun _ : attribute T => v) atts)
  by (intro v; rewrite map_map; reflexivity).
rewrite M.
destruct (first_error O (map (ev ce env) args)) as [e | ].
- rewrite C; constructor; [apply err_row_RT, frow_RT | constructor].
- destruct (table_fun O name) as [f | ]; [ | rewrite C; constructor; [apply err_row_RT, frow_RT | constructor]].
  apply F2_map; intros [i l] _; apply frow_RT.
Qed.

(** ** SELECT blocks *)

Definition r_g (g : sgroup T relname) : sgroup T relname :=
  match g with
  | G_Fine _ _ => G_Fine T relname
  | G_By l => G_By (map r_e l)
  | G_Sets ss => G_Sets (map (map r_e) ss)
  | G_Rollup l => G_Rollup (map r_e l)
  | G_Cube l => G_Cube (map r_e l)
  end.

Definition r_sel (s : sselect T relname) : sselect T relname :=
  match s with
  | S_Star _ _ => S_Star T relname
  | S_List l => S_List (map (fun it => match it with S_As e a => S_As (r_e e) (rho a) end) l)
  end.

Lemma from_sort_R : forall lf ce' ce, Rsort ce' ce ->
  Fset.Union (A T) (map (sfrom_sort ORN basesort' ce') (map rf lf)) =S= rs (Fset.Union (A T) (map (sfrom_sort ORN basesort ce) lf)).
Proof.
intros lf ce' ce R0; rewrite (Fset.equal_eq_2 _ _ _ _ (rs_Union _)), map_map, map_map; apply Union_eq_F2.
apply F2_map; intros f _; apply sort_rename_f; exact R0.
Qed.

Lemma where_R : forall lf w ce' ce env' env, RCE ce' ce -> REnv env' env -> (forall f, In f lf -> Ef f) -> Ec w ->
  RL (where_rows ORN O basesort' instance' ce' env' (map rf lf) (rc w)) (where_rows ORN O basesort instance ce env lf w).
Proof.
intros lf w ce' ce env' env Hc He Hf Hw; unfold where_rows; cbv zeta.
apply (F2_flat_map _ _ _ _ RT).
- apply (F2_fold_left _ _ _ _ RL RL).
  + rewrite map_map; apply F2_map; intros f If; apply (Hf f If); assumption.
  + constructor; [apply RT_empty | constructor].
  + intros a1 a2 x1 x2 Ha Hx; apply keep_errors_R; [ | apply RL_app; assumption].
    unfold cross_product; apply (F2_flat_map _ _ _ _ RT); [exact Ha | intros t' t Ht].
    apply (F2_map2 _ _ _ _ _ RT); [exact Hx | intros; apply RT_join; assumption].
- intros t' t Ht; destruct (Hw ce' ce _ _ Hc (REnv_t _ _ _ _ Ht He)) as [E1 E2].
  rewrite (row_error_RT _ _ Ht), E1, E2; destruct (_ || _); [constructor; [apply err_row_RT; exact Ht | constructor] | ].
  destruct (is_true3 T _); constructor; [exact Ht | constructor].
Qed.

Definition gE (g : sgroup T relname) : Prop :=
  match g with
  | G_Fine _ _ => True
  | G_By l | G_Rollup l | G_Cube l => LE T relname Ee l
  | G_Sets ss => forall l, In l ss -> LE T relname Ee l
  end.

Lemma gk_R : forall g ce' ce env' env t' t, gE g -> RCE ce' ce -> REnv env' env -> RT t' t ->
  gkeys_of ORN O basesort' instance' ce' env' (r_g g) t' = gkeys_of ORN O basesort instance ce env g t /\
  row_vals_of ORN O basesort' instance' ce' env' (r_g g) t' = row_vals_of ORN O basesort instance ce env g t.
Proof.
intros g ce' ce env' env t' t Hg Hc He Ht; assert (E := REnv_t _ _ _ _ Ht He).
assert (M : forall l, LE T relname Ee l ->
   map (ev' ce' (slice_t T relname t' :: env')) (map re l) = map (ev ce (slice_t T relname t :: env)) l)
  by (intros l Hl; rewrite map_map; apply map_ext_in; intros y Hy; apply (Hl y Hy); assumption).
destruct g as [ | l | ss | l | l]; simpl in Hg; unfold gkeys_of, row_vals_of, r_g; try (split; trivial; apply M; exact Hg).
assert (G : (fix go (ss : list (list (SqlFull.sexpr T relname))) : list (value T) :=
               match ss with nil => nil | l :: r => map (ev' ce' (slice_t T relname t' :: env')) l ++ go r end) (map (map re) ss) =
            (fix go (ss : list (list (SqlFull.sexpr T relname))) : list (value T) :=
               match ss with nil => nil | l :: r => map (ev ce (slice_t T relname t :: env)) l ++ go r end) ss).
{ induction ss as [ | l0 ss IH]; [reflexivity | ]; cbn [map]; f_equal;
    [apply M; apply Hg; left; reflexivity | apply IH; intros l1 Hl1; apply Hg; right; exact Hl1]. }
split; exact G.
Qed.

Lemma implicit_R : forall ce' ce sa' sa s h ex, Rsort ce' ce -> sa' =S= rs sa ->
  implicit_group ORN basesort' ce' sa' (r_sel s) (rc h) (map re ex) = implicit_group ORN basesort ce sa s h ex.
Proof.
intros ce' ce sa' sa s h ex R0 Hs; unfold implicit_group.
rewrite (has_agg_c h ce' ce sa' sa R0 Hs); f_equal; [f_equal | ].
- destruct s as [ | l]; [reflexivity | ]; simpl; rewrite existsb_map'; apply existsb_ext'; intros [e a].
  apply has_agg_e; assumption.
- rewrite existsb_map'; apply existsb_ext'; intro e; apply has_agg_e; assumption.
Qed.

Lemma filter_map_re : forall (p' p : SqlFull.sexpr T relname -> bool) l, (forall x, p' (re x) = p x) ->
  filter p' (map re l) = map re (filter p l).
Proof. intros p' p l H; induction l as [ | x l IH]; simpl; [reflexivity | rewrite H; destruct (p x); simpl; rewrite IH; reflexivity]. Qed.

Lemma sdedup_re : forall l seen, sdedup (map re seen) (map re l) = map re (sdedup seen l).
Proof.
intro l; induction l as [ | e l IH]; intro seen; simpl; [reflexivity | ].
rewrite existsb_eqb_re; destruct (existsb (sexpr_eqb e) seen); [apply IH | ].
simpl; f_equal; exact (IH (e :: seen)).
Qed.

Lemma F2_flat_map_same : forall (X X' Y' : Type) (Q : X' -> Y' -> Prop) (f : X -> list X') (g : X -> list Y') l,
  (forall x, In x l -> Forall2 Q (f x) (g x)) -> Forall2 Q (flat_map f l) (flat_map g l).
Proof.
intros X X' Y' Q f g l H; induction l as [ | x l IH]; simpl; [constructor | ].
apply Forall2_app; [apply H; left; reflexivity | apply IH; intros; apply H; right; assumption].
Qed.

(** the groups, with the grouping expressions which they hide *)
Definition RG (p' p : list (tuple T) * list (SqlFull.sexpr T relname)) := RL (fst p') (fst p) /\ snd p' = map re (snd p).

Lemma set_groupings_R : forall (rv' rv : tuple T -> list (value T)) univ positions rows' rows,
  (forall t' t, RT t' t -> rv' t' = rv t) -> RL rows' rows ->
  Forall2 RG (set_groupings O rv' (map re univ) positions rows') (set_groupings O rv univ positions rows).
Proof.
intros rv' rv univ positions rows' rows Hrv H; unfold set_groupings.
apply F2_flat_map_same; intros pos _; cbv zeta.
assert (S : map (fun i => nth i (map re univ) (E_Const T relname (null O))) pos =
            map re (map (fun i => nth i univ (E_Const T relname (null O))) pos)).
{ rewrite map_map; apply map_ext; intro i.
  change (E_Const T relname (null O)) with (re (E_Const T relname (null O))) at 1; apply map_nth. }
rewrite S.
rewrite (filter_map_re _ (fun e => negb (existsb (sexpr_eqb e) (map (fun i => nth i univ (E_Const T relname (null O))) pos))))
  by (intro x; rewrite existsb_eqb_re; reflexivity).
rewrite (sdedup_re _ nil).
apply (F2_map2 _ _ _ _ _ RL); [ | intros x y Hxy; split; [exact Hxy | reflexivity]].
destruct pos as [ | i pos]; [constructor; [exact H | constructor] | ].
apply F2_group_on; [exact H | intros x y Hxy; rewrite (Hrv _ _ Hxy); reflexivity].
Qed.

Lemma grouping_R' : forall g (gk' gk rv' rv : tuple T -> list (value T)) imp rows' rows,
  (forall t' t, RT t' t -> gk' t' = gk t) -> (forall t' t, RT t' t -> rv' t' = rv t) -> RL rows' rows ->
  Forall2 RG (grouping_part O (r_g g) gk' rv' imp rows') (grouping_part O g gk rv imp rows).
Proof.
intros g gk' gk rv' rv imp rows' rows Hgk Hrv H; unfold grouping_part; cbv zeta.
assert (K : RL (map (fun t => if existsb (is_error O) (gk' t) then err_row O t else t) rows')
               (map (fun t => if existsb (is_error O) (gk t) then err_row O t else t) rows)).
{ apply (F2_map2 _ _ _ _ _ _ _ _ _ _ H); intros t' t Ht; rewrite (Hgk _ _ Ht); destruct (existsb _ _); [apply err_row_RT | ]; exact Ht. }
assert (N : forall (l' l : list (list (tuple T))), Forall2 RL l' l ->
  Forall2 RG (map (fun grp => (grp, @nil (SqlFull.sexpr T relname))) l') (map (fun grp => (grp, @nil (SqlFull.sexpr T relname))) l))
  by (intros l' l Hl; apply (F2_map2 _ _ _ _ _ _ _ _ _ _ Hl); intros x y Hxy; split; [exact Hxy | reflexivity]).
destruct g as [ | l | ss | l | l]; cbn [r_g].
- apply N; destruct imp; [constructor; [exact K | constructor] | ].
  apply (F2_map2 _ _ _ _ _ _ _ _ _ _ K); intros; constructor; [assumption | constructor].
- apply N; destruct l as [ | e l]; [constructor; [exact K | constructor] | ].
  apply F2_group_on; [exact K | exact Hgk].
- rewrite <- concat_map.
  replace ((fix go (off : nat) (ss0 : list (list (SqlFull.sexpr T relname))) : list (list nat) :=
              match ss0 with nil => nil | l :: r => seq off (length l) :: go (off + length l)%nat r end) 0%nat (map (map re) ss))
    with ((fix go (off : nat) (ss0 : list (list (SqlFull.sexpr T relname))) : list (list nat) :=
              match ss0 with nil => nil | l :: r => seq off (length l) :: go (off + length l)%nat r end) 0%nat ss).
  + apply set_groupings_R; assumption.
  + generalize 0%nat; induction ss as [ | l ss IH]; intro off; [reflexivity | ]; cbn [map]; rewrite map_length; f_equal; apply IH.
- rewrite map_length; apply set_groupings_R; assumption.
- rewrite map_length; apply set_groupings_R; assumption.
Qed.

Lemma mk_row_RT : forall l : list (attribute T * value T), RT (mk_row O (map (fun p => (rho (fst p), snd p)) l)) (mk_row O l).
Proof.
intro l; unfold mk_row; apply RT_mk_tuple.
- rewrite Fset.equal_spec; intro b; rewrite (Fset.mem_eq_2 _ _ _ (rs_mk_set _)), !map_map; reflexivity.
- intros a _; induction l as [ | [b v] l IH]; simpl; [apply null_of_rho | ].
  rewrite rho_eqb; destruct (Oset.eq_bool (OAtt T) a b); [apply store_rho | exact IH].
Qed.

Definition sE (s : sselect T relname) : Prop :=
  match s with S_Star _ _ => True | S_List l => forall e a, In (S_As e a) l -> Ee e end.

Lemma group_error_R : forall ge' ge, REnv ge' ge ->
  match ge' with (_, gr, _) :: _ => existsb (row_error O) gr | nil => false end =
  match ge with (_, gr, _) :: _ => existsb (row_error O) gr | nil => false end.
Proof.
intros ge' ge H; destruct H as [ | [[sa' g'] h'] [[sa g] h] X Y [_ [S2 _]] _]; [reflexivity | ].
apply (F2_existsb _ _ RT); [exact S2 | apply row_error_RT].
Qed.

Lemma select_rest_R : forall s h sa' sa sq gs' gs ce' ce env' env, RCE ce' ce -> REnv env' env -> sa' =S= rs sa ->
  sE s -> Ec h -> Forall2 RG gs' gs ->
  Forall2 RP (select_rest ORN O basesort' instance' ce' env' sa' sq (r_sel s) (rc h) gs')
             (select_rest ORN O basesort instance ce env sa sq s h gs).
Proof.
intros s h sa' sa sq gs' gs ce' ce env' env Hc He Hsa Hs Hh Hg; unfold select_rest; cbv zeta.
assert (G : Forall2 REnv (map (fun gh => slice_gs sa' (fst gh) (snd gh) :: env') gs') (map (fun gh => slice_gs sa (fst gh) (snd gh) :: env) gs)).
{ apply (F2_map2 _ _ _ _ _ _ _ _ _ _ Hg); intros [g' h'] [g0 h0] [E1 E2]; simpl in E1, E2; subst h'; apply REnv_gs; assumption. }
match goal with |- Forall2 RP match sq with Set_All => ?o' | _ => _ end match sq with Set_All => ?o | _ => _ end =>
  assert (K : Forall2 RP o' o) end.
- apply (F2_map2 _ _ _ _ _ (fun x y : SqlFull.senv T relname * bool => REnv (fst x) (fst y) /\ snd x = snd y)).
  + apply F2_filter.
    * apply (F2_map2 _ _ _ _ _ _ _ _ _ _ G); intros x y Hxy; split; [exact Hxy | cbn [snd]].
      f_equal; [exact (group_error_R _ _ Hxy) | exact (proj2 (Hh ce' ce _ _ Hc Hxy))].
    * intros x y [Hxy E]; rewrite E, (proj1 (Hh ce' ce _ _ Hc Hxy)); reflexivity.
  + intros [x b'] [y b] [Hxy E]; simpl in Hxy, E; subst b'; simpl; split; [ | exact Hxy].
    assert (W : RT match r_sel s with
                   | S_Star _ _ => match x with (_, t :: _, _) :: _ => t | _ => null_tuple T sa' end
                   | S_List l => mk_row O (map (fun it => match it with S_As e a => (a, ev' ce' x e) end) l)
                   end
                   match s with
                   | S_Star _ _ => match y with (_, t :: _, _) :: _ => t | _ => null_tuple T sa end
                   | S_List l => mk_row O (map (fun it => match it with S_As e a => (a, ev ce y e) end) l)
                   end).
    { destruct s as [ | l]; cbn [r_sel].
      - destruct Hxy as [ | [[sx gx] hx] [[sy gy] hy] X Y [_ [S2 _]] _]; [apply null_tuple_RT; exact Hsa | ].
        simpl in S2; destruct S2; [apply null_tuple_RT; exact Hsa | assumption].
      - replace (map (fun it => match it with S_As e a => (a, ev' ce' x e) end)
                     (map (fun it => match it with S_As e a => S_As (re e) (rho a) end) l))
          with (map (fun p : attribute T * value T => (rho (fst p), snd p))
                    (map (fun it => match it with S_As e a => (a, ev ce y e) end) l)); [apply mk_row_RT | ].
        rewrite !map_map; apply map_ext_in; intros [e a] Hea; simpl; f_equal; symmetry; apply (Hs e a Hea); assumption. }
    destruct b; [apply err_row_RT | ]; exact W.
- destruct sq; [exact K | ].
  apply F2_dedup_on; [intros x y [Hxy _]; exact Hxy | exact K].
Qed.

Lemma s_spec : forall sq s lf w g h,
  match s with S_Star _ _ => True | S_List l => forall e a, In (S_As e a) l -> Ee e end ->
  (forall f, In f lf -> Ef f) -> Ec w ->
  match g with
  | G_Fine _ _ => True
  | G_By l | G_Rollup l | G_Cube l => LE T relname Ee l
  | G_Sets ss => forall l, In l ss -> LE T relname Ee l
  end -> Ec h -> Es (Select sq s lf w g h).
Proof.
intros sq s lf w g h Hs Hf Hw Hg Hh ce' ce env' env ex Hc He.
change (rsp (Select sq s lf w g h)) with (Select sq (r_sel s) (map rf lf) (rc w) (r_g g) (rc h)).
rewrite !eval_select; cbv zeta.
assert (R0 := RCE_Rsort _ _ Hc); assert (Sa := from_sort_R lf ce' ce R0).
rewrite (implicit_R ce' ce _ _ s h ex R0 Sa).
apply select_rest_R; trivial.
apply grouping_R'; [ | | apply where_R; assumption].
- intros t' t Ht; exact (proj1 (gk_R g ce' ce env' env t' t Hg Hc He Ht)).
- intros t' t Ht; exact (proj2 (gk_R g ce' ce env' env t' t Hg Hc He Ht)).
Qed.

(** * The theorem *)

Theorem eval_rename_gen : forall q, Eqr q.
Proof.
intro q; exact (ind_q T relname Ee Ec Eqr Es Ef e_const e_col e_fun e_agg e_aggx e_case e_cond e_sub e_grouping
                  e_conj e_not e_true e_pred e_expr e_quant e_in e_exists q_table q_set q_select q_order q_fetch
                  q_window q_with q_withrec s_spec fr_query fr_join fr_fun q).
Qed.

(** The rows of the renamed query, over the renamed database, are the renamed rows of the query, in the same
    order. *)
Theorem eval_rename : forall q,
  RL (eval_query_list ORN O basesort' instance' (rq q)) (eval_query_list ORN O basesort instance q).
Proof. intro q; unfold eval_query_list; apply eval_rename_gen; constructor. Qed.
(** A query fails over the renamed database when it fails over the database, and gives the renamed rows otherwise. *)
Corollary eval_result_rename : forall q,
  match eval_query_result ORN O basesort' instance' (rq q), eval_query_result ORN O basesort instance q with
  | QR_Rows _ l', QR_Rows _ l => RL l' l
  | QR_Error _, QR_Error _ => True
  | _, _ => False
  end.
Proof.
intro q; unfold eval_query_result; cbv zeta; assert (K := eval_rename q).
rewrite (F2_existsb _ _ _ _ _ _ _ K row_error_RT).
destruct (existsb (row_error O) (eval_query_list ORN O basesort instance q)); [exact I | exact K].
Qed.

End Sec.
