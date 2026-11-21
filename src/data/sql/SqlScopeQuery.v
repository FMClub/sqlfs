(** * Scoping of whole queries (TODO 6.2)

    A query reads the enclosing blocks only through the columns which it names ([atts_q]): its evaluation in
    [p ++ env1] and in [p ++ env2], for a non empty [p] (the blocks between the query and [env1], [env2], the
    innermost one at least), is the same when [env1] and [env2] bind none of these columns ([scope_query]); in
    particular a query in a block depends on the blocks further out only through the columns which it names
    ([scope_block]). This holds for subqueries, aggregates (an aggregate belongs to the innermost block which binds
    one of its columns, [agg_env]), windows, [WITH] and [WITH RECURSIVE], [ORDER BY] and [FETCH].
    - The condition on names cannot be dropped: a failed row of an operand of a product has the columns of its
      operand only ([SqlSorts.v]), so that an expression of the block over the columns of the other operand reads
      them from the enclosing blocks when they bind them.
    - The innermost block is common to both environments: the arguments of a table function of the [FROM] clause are
      evaluated in the environment of the block itself, and they see its hidden grouping expressions.
    [cols_atts]: the columns which a query reads from outside itself ([squery_cols], the condition of [wf_query])
    occur in it. *)
Require Import List Bool String NArith FunctionalExtensionality.
Require Import BasicFacts ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection FlatData SqlFull SqlInduction
        SqlFullFacts SqlCongruence.

Section Atts.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.

Notation sexpr := (sexpr T relname).
Notation scond := (scond T relname).
Notation squery := (squery T relname).
Notation sspec := (sspec T relname).
Notation sfrom := (sfrom T relname).

(** the columns which occur in a query *)
Fixpoint atts_e (e : sexpr) {struct e} : list (Tuple.attribute T) :=
  match e with
  | E_Const _ _ _ => nil
  | E_Col _ _ a => a :: nil
  | E_Fun _ l => flat_map atts_e l
  | E_Agg _ _ e c => atts_e e ++ atts_c c
  | E_AggX _ _ e sep lo c =>
    atts_e e ++ atts_c c ++ (match sep with Some s => atts_e s | None => nil end) ++
    flat_map (fun o => match o with O_By e _ _ => atts_e e end) lo
  | E_Case c e1 e2 => atts_c c ++ atts_e e1 ++ atts_e e2
  | E_Cond c => atts_c c
  | E_Sub q => atts_q q
  | E_Grouping e => atts_e e
  end
with atts_c (c : scond) {struct c} : list (Tuple.attribute T) :=
  match c with
  | C_Conj _ c1 c2 => atts_c c1 ++ atts_c c2
  | C_Not c => atts_c c
  | C_True _ _ => nil
  | C_Pred _ l => flat_map atts_e l
  | C_Expr e => atts_e e
  | C_Quant _ _ l q _ | C_In l q _ => flat_map atts_e l ++ atts_q q
  | C_Exists q => atts_q q
  end
with atts_q (q : squery) {struct q} : list (Tuple.attribute T) :=
  match q with
  | SQ_Table _ _ => nil
  | SQ_Set _ _ q1 q2 | SQ_With _ q1 q2 => atts_q q1 ++ atts_q q2
  | SQ_Select sp => atts_s sp
  | SQ_Order q lo _ _ | SQ_Fetch q lo _ _ _ _ => atts_q q ++ flat_map (fun o => match o with O_By e _ _ => atts_e e end) lo
  | SQ_Window q lw =>
    atts_q q ++ flat_map (fun w => match w with
                                   | W_As f lp lo _ =>
                                     flat_map atts_e lp ++ flat_map (fun o => match o with O_By e _ _ => atts_e e end) lo ++
                                     (fix fw (f : swfun T relname) : list (Tuple.attribute T) :=
                                        match f with
                                        | W_Agg _ _ e _ | W_First_Value e _ | W_Last_Value e _ | W_Nth_Value e _ _ => atts_e e
                                        | W_Lag e _ d | W_Lead e _ d => atts_e e ++ atts_e d
                                        | W_Opts f' _ _ => fw f'
                                        | _ => nil
                                        end) f
                                   end) lw
  | SQ_WithRec _ _ q1 q2 q3 => atts_q q1 ++ atts_q q2 ++ atts_q q3
  end
with atts_s (sp : sspec) {struct sp} : list (Tuple.attribute T) :=
  match sp with
  | Select _ s lf w g h =>
    (match s with S_Star _ _ => nil | S_List l => flat_map (fun x => match x with S_As e _ => atts_e e end) l end) ++
    flat_map atts_f lf ++ atts_c w ++
    (match g with
     | G_Fine _ _ => nil
     | G_By l | G_Rollup l | G_Cube l => flat_map atts_e l
     | G_Sets ss => flat_map (flat_map atts_e) ss
     end) ++ atts_c h
  end
with atts_f (f : sfrom) {struct f} : list (Tuple.attribute T) :=
  match f with
  | Fr_Query q _ => atts_q q
  | Fr_Join _ _ f1 f2 c => atts_f f1 ++ atts_f f2 ++ atts_c c
  | Fr_Fun _ args _ _ => flat_map atts_e args
  end.

End Atts.

Section Cols.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.
Hypothesis ORN : Oset.Rcd relname.
Hypothesis basesort : relname -> Fset.set (Tuple.A T).

Notation sc_e := (sexpr_cols ORN basesort).
Notation sc_c := (scond_cols ORN basesort).
Notation sc_q := (squery_cols ORN basesort).
Notation sc_s := (sspec_cols ORN basesort).
Notation sc_f := (sfrom_cols ORN basesort).

Lemma incl_flat_map : forall (X Y : Type) (f g : X -> list Y) l, (forall x, In x l -> incl (f x) (g x)) ->
  incl (flat_map f l) (flat_map g l).
Proof.
intros X Y f g l H y Hy; apply in_flat_map in Hy; destruct Hy as [x [Hx Hy]]; apply in_flat_map; exists x; split;
  [exact Hx | exact (H x Hx y Hy)].
Qed.

Lemma in_go_sets : forall ce (ss : list (list (sexpr T relname))) x,
  In x ((fix go (ss : list (list (sexpr T relname))) : list (Tuple.attribute T) :=
           match ss with nil => nil | l :: r => flat_map (sc_e ce) l ++ go r end) ss) ->
  exists l, In l ss /\ In x (flat_map (sc_e ce) l).
Proof.
intros ce ss x; induction ss as [ | l ss IH]; intro H; [destruct H | ].
apply in_app_or in H; destruct H as [H | H]; [exists l; split; [left; reflexivity | exact H] | ].
destruct (IH H) as [l' [H1 H2]]; exists l'; split; [right; exact H1 | exact H2].
Qed.

Ltac fin :=
  first [ assumption
        | solve [left; fin] | solve [right; fin]
        | match goal with H : In ?y ?l |- exists z, In z ?l /\ _ => exists y; split; [exact H | fin] end
        | match goal with |- In _ (match ?m with _ => _ end) => destruct m; fin end
        | match goal with |- In _ (flat_map _ _) => rewrite List.in_flat_map; fin end
        | match goal with |- In _ (_ ++ _) => rewrite List.in_app_iff; fin end ].

Ltac solve_incl :=
  let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
  repeat match goal with
         | H : In x (_ ++ _) |- _ => apply in_app_or in H; destruct H as [H | H]
         | H : In x (flat_map _ _) |- _ => apply in_flat_map in H; destruct H as [? [? H]]
         | H : In x (filter _ _) |- _ => apply filter_In in H; destruct H as [H _]
         | H : In x nil |- _ => destruct H
         | H : In x (?F ?ss) |- _ => apply in_go_sets in H; destruct H as [? [? H]]
         | H : In x (match ?m with _ => _ end) |- _ => destruct m
         | H : In ?o _, K : In x (match ?o with _ => _ end) |- _ => destruct o
         end;
  repeat match goal with
         | IH : forall ce, incl (_ ce ?e) _, H : In x (_ ?ce ?e) |- _ => apply (IH ce) in H
         | IH : forall y, In y ?l -> forall ce, incl (_ ce y) _, Hy : In ?y ?l, H : In x (_ ?ce ?y) |- _ =>
           apply (IH y Hy ce) in H
         | IH : forall e d n, In (O_By e d n) ?l -> forall ce, incl (_ ce e) _, Hy : In (O_By ?y ?d ?n) ?l,
           H : In x (_ ?ce ?y) |- _ => apply (IH y d n Hy ce) in H
         | IH : forall e a, In (S_As e a) ?l -> forall ce, incl (_ ce e) _, Hy : In (S_As ?y ?a) ?l,
           H : In x (_ ?ce ?y) |- _ => apply (IH y a Hy ce) in H
         | IH : forall l, In l ?ss -> forall y, In y l -> forall ce, incl (_ ce y) _, Hl : In ?l ?ss, Hy : In ?y ?l,
           H : In x (_ ?ce ?y) |- _ => apply (IH l Hl y Hy ce) in H
         | IH : forall s, ?sep = Some s -> forall ce, incl (_ ce s) _, H : In x (_ ?ce ?s) |- _ =>
           apply (IH s eq_refl ce) in H
         end;
  rewrite ?List.in_app_iff, ?List.in_flat_map; fin.

Theorem cols_atts : forall q ce, incl (sc_q ce q) (atts_q T relname q).
Proof.
apply (ind_q T relname
  (fun e => forall ce, incl (sc_e ce e) (atts_e T relname e))
  (fun c => forall ce, incl (sc_c ce c) (atts_c T relname c))
  (fun q => forall ce, incl (sc_q ce q) (atts_q T relname q))
  (fun sp => forall ce, incl (sc_s ce sp) (atts_s T relname sp))
  (fun f => forall ce, incl (sc_f ce f) (atts_f T relname f))); unfold LE, LO; intros;
  cbn [sexpr_cols scond_cols squery_cols sspec_cols sfrom_cols atts_e atts_c atts_q atts_s atts_f];
  fold (sc_e ce) (sc_c ce) (sc_q ce) (sc_s ce) (sc_f ce)
       (atts_e T relname) (atts_c T relname) (atts_q T relname) (atts_s T relname) (atts_f T relname);
  try solve [solve_incl].
Qed.

Theorem cols_atts_e : forall e ce, incl (sc_e ce e) (atts_e T relname e).
Proof.
apply (ind_e T relname
  (fun e => forall ce, incl (sc_e ce e) (atts_e T relname e))
  (fun c => forall ce, incl (sc_c ce c) (atts_c T relname c))
  (fun q => forall ce, incl (sc_q ce q) (atts_q T relname q))
  (fun sp => forall ce, incl (sc_s ce sp) (atts_s T relname sp))
  (fun f => forall ce, incl (sc_f ce f) (atts_f T relname f))); unfold LE, LO; intros;
  cbn [sexpr_cols scond_cols squery_cols sspec_cols sfrom_cols atts_e atts_c atts_q atts_s atts_f];
  fold (sc_e ce) (sc_c ce) (sc_q ce) (sc_s ce) (sc_f ce)
       (atts_e T relname) (atts_c T relname) (atts_q T relname) (atts_s T relname) (atts_f T relname);
  try solve [solve_incl].
Qed.

Theorem cols_atts_c : forall c ce, incl (sc_c ce c) (atts_c T relname c).
Proof.
apply (ind_c T relname
  (fun e => forall ce, incl (sc_e ce e) (atts_e T relname e))
  (fun c => forall ce, incl (sc_c ce c) (atts_c T relname c))
  (fun q => forall ce, incl (sc_q ce q) (atts_q T relname q))
  (fun sp => forall ce, incl (sc_s ce sp) (atts_s T relname sp))
  (fun f => forall ce, incl (sc_f ce f) (atts_f T relname f))); unfold LE, LO; intros;
  cbn [sexpr_cols scond_cols squery_cols sspec_cols sfrom_cols atts_e atts_c atts_q atts_s atts_f];
  fold (sc_e ce) (sc_c ce) (sc_q ce) (sc_s ce) (sc_f ce)
       (atts_e T relname) (atts_c T relname) (atts_q T relname) (atts_s T relname) (atts_f T relname);
  try solve [solve_incl].
Qed.

End Cols.

Section F2.

Variables X Y : Type.
Variable P : X -> Y -> Prop.

Lemma F2_map : forall (Z : Type) (f : Z -> X) (g : Z -> Y) l, (forall z, In z l -> P (f z) (g z)) ->
  Forall2 P (map f l) (map g l).
Proof. intros Z f g l H; induction l as [ | z l IH]; constructor; [apply H; left; reflexivity | apply IH; intros; apply H; right; assumption]. Qed.

Lemma F2_map2 : forall (X' Y' : Type) (Q : X' -> Y' -> Prop) (f : X' -> X) (g : Y' -> Y) l1 l2,
  Forall2 Q l1 l2 -> (forall x y, Q x y -> P (f x) (g y)) -> Forall2 P (map f l1) (map g l2).
Proof. intros X' Y' Q f g l1 l2 H K; induction H; constructor; auto. Qed.

Lemma F2_filter : forall p q l1 l2, Forall2 P l1 l2 -> (forall x y, P x y -> p x = q y) ->
  Forall2 P (filter p l1) (filter q l2).
Proof. intros p q l1 l2 H K; induction H as [ | x y l1 l2 Hxy H IH]; [constructor | simpl; rewrite (K x y Hxy)]. destruct (q y); [constructor; assumption | assumption]. Qed.

Lemma F2_app : forall l1 l2 l1' l2', Forall2 P l1 l2 -> Forall2 P l1' l2' -> Forall2 P (l1 ++ l1') (l2 ++ l2').
Proof. intros l1 l2 l1' l2' H K; induction H; simpl; [exact K | constructor; assumption]. Qed.

Lemma F2_firstn : forall n l1 l2, Forall2 P l1 l2 -> Forall2 P (firstn n l1) (firstn n l2).
Proof. intro n; induction n as [ | n IH]; intros l1 l2 H; [constructor | destruct H; simpl; constructor; auto]. Qed.

Lemma F2_skipn : forall n l1 l2, Forall2 P l1 l2 -> Forall2 P (skipn n l1) (skipn n l2).
Proof. intro n; induction n as [ | n IH]; intros l1 l2 H; [exact H | destruct H; simpl; [constructor | auto]]. Qed.

Lemma F2_length : forall l1 l2, Forall2 P l1 l2 -> List.length l1 = List.length l2.
Proof. intros l1 l2 H; induction H; simpl; congruence. Qed.

Lemma F2_merge : forall le1 le2, (forall x1 y1 x2 y2, P x1 y1 -> P x2 y2 -> le1 x1 x2 = le2 y1 y2) ->
  forall a1 a2, Forall2 P a1 a2 -> forall b1 b2, Forall2 P b1 b2 -> Forall2 P (merge le1 a1 b1) (merge le2 a2 b2).
Proof.
intros le1 le2 K a1 a2 Ha; induction Ha as [ | x1 x2 a1 a2 Hx Ha IHa]; intros b1 b2 Hb.
- destruct Hb; simpl; [constructor | constructor; assumption].
- induction Hb as [ | y1 y2 b1 b2 Hy Hb IHb]; [simpl; constructor; assumption | ].
  simpl; rewrite (K x1 x2 y1 y2 Hx Hy); destruct (le2 x2 y2); constructor; trivial.
  + apply IHa; constructor; assumption.
Qed.

Lemma F2_msort_fuel : forall le1 le2, (forall x1 y1 x2 y2, P x1 y1 -> P x2 y2 -> le1 x1 x2 = le2 y1 y2) ->
  forall n l1 l2, Forall2 P l1 l2 -> Forall2 P (msort_fuel le1 n l1) (msort_fuel le2 n l2).
Proof.
intros le1 le2 K n; induction n as [ | n IH]; intros l1 l2 H; [exact H | ].
destruct H as [ | x1 x2 l1 l2 Hx H]; [constructor | ].
destruct H as [ | y1 y2 l1 l2 Hy H]; [simpl; constructor; [assumption | constructor] | ].
cbn [msort_fuel]; rewrite (F2_length (x1 :: y1 :: l1) (x2 :: y2 :: l2)) by (constructor; [ | constructor]; assumption).
assert (L : Forall2 P (x1 :: y1 :: l1) (x2 :: y2 :: l2)) by (constructor; [ | constructor]; assumption).
apply (F2_merge le1 le2 K); [apply IH, F2_firstn, L | apply IH, F2_skipn, L].
Qed.

End F2.

Section Scope.


Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.
Hypothesis ORN : Oset.Rcd relname.
Hypothesis O : dialect T.
Hypothesis basesort : relname -> Fset.set (Tuple.A T).
Hypothesis instance : relname -> Febag.bag (Fecol.CBag (Tuple.CTuple T)).

Notation senv := (senv T relname).
Notation mem a s := (Fset.mem (Tuple.A T) a s).

Variables env1 env2 : senv.
Variable U : list (Tuple.attribute T).

Definition unbound (env : senv) (a : Tuple.attribute T) := forall s, In s env -> mem a (fst (fst s)) = false.

Hypothesis F1 : forall a, In a U -> unbound env1 a.
Hypothesis F2 : forall a, In a U -> unbound env2 a.

Inductive R : senv -> senv -> Prop :=
  | R_base : forall s, R (s :: env1) (s :: env2)
  | R_cons : forall s A B, R A B -> R (s :: A) (s :: B).

Definition Rq (A B : senv) := R A B \/ (A = env1 /\ B = env2).

Lemma R_head : forall X Y, R X Y -> exists s X' Y', X = s :: X' /\ Y = s :: Y'.
Proof. intros X Y H; destruct H as [s | s A B _]; do 3 eexists; split; reflexivity. Qed.

Lemma Rq_cons : forall s A B, Rq A B -> R (s :: A) (s :: B).
Proof. intros s A B [H | [-> ->]]; [apply R_cons; exact H | apply R_base]. Qed.

Lemma R_Rq : forall A B, R A B -> Rq A B.
Proof. intros A B H; left; exact H. Qed.

Lemma lookup_unbound : forall env a, unbound env a -> lookup env a = null_of T a.
Proof.
intros env a; induction env as [ | [[sa g] h] env IH]; intro H; [reflexivity | ]; simpl.
assert (K : mem a sa = false) by exact (H _ (or_introl eq_refl)); rewrite K.
apply IH; intros s Hs; apply H; right; exact Hs.
Qed.

Lemma lookup_R : forall A B a, R A B -> In a U -> lookup A a = lookup B a.
Proof.
intros A B a H Ha; induction H as [[[sa g] h] | [[sa g] h] A B H IH]; simpl.
- destruct (mem a sa); [reflexivity | ].
  rewrite (lookup_unbound env1 a (F1 a Ha)), (lookup_unbound env2 a (F2 a Ha)); reflexivity.
- destruct (mem a sa); [reflexivity | exact IH].
Qed.

Lemma is_hidden_R : forall A B e, R A B -> is_hidden A e = is_hidden B e.
Proof. intros A B e H; destruct H; reflexivity. Qed.

Lemma agg_env_rec_unbound : forall cols env, (forall a, In a cols -> unbound env a) -> agg_env_rec cols env = nil.
Proof.
intros cols env; induction env as [ | [[sa g] h] env IH]; intro H; [reflexivity | ]; simpl.
replace (existsb (fun a => mem a sa) cols) with false.
- apply IH; intros a Ha s Hs; apply (H a Ha); right; exact Hs.
- symmetry; apply Bool.not_true_iff_false; intro K; apply existsb_exists in K; destruct K as [a [Ha K]].
  assert (K' : mem a sa = false) by exact (H a Ha _ (or_introl eq_refl)); rewrite K' in K; discriminate.
Qed.

Lemma agg_env_rec_R : forall cols A B, incl cols U -> R A B ->
  (agg_env_rec cols A = nil /\ agg_env_rec cols B = nil) \/ R (agg_env_rec cols A) (agg_env_rec cols B).
Proof.
intros cols A B Hc H; induction H as [[[sa g] h] | [[sa g] h] A B H IH]; simpl.
- destruct (existsb _ cols); [right; apply R_base | left].
  split; apply agg_env_rec_unbound; intros a Ha; [apply F1 | apply F2]; apply Hc; exact Ha.
- destruct (existsb _ cols); [right; apply R_cons; exact H | exact IH].
Qed.

Lemma agg_env_R : forall cols A B, incl cols U -> R A B -> R (agg_env cols A) (agg_env cols B).
Proof.
intros cols A B Hc H; unfold agg_env.
destruct (agg_env_rec_R cols A B Hc H) as [[-> ->] | K]; [exact H | ].
destruct K; exact (R_cons _ _ _ K) || (simpl; first [apply R_base | apply R_cons; assumption]).
Qed.

(** * The theorem *)

Notation ev := (eval_sexpr ORN O basesort instance).
Notation ec := (eval_scond ORN O basesort instance).
Notation er := (scond_raises ORN O basesort instance).
Notation eq_ := (eval_squery ORN O basesort instance).
Notation es := (eval_sspec ORN O basesort instance).
Notation ef := (eval_sfrom ORN O basesort instance).

Definition RL (l1 l2 : list (Tuple.tuple T * senv)) := Forall2 (fun x y => fst x = fst y /\ R (snd x) (snd y)) l1 l2.

Definition Ve (e : sexpr T relname) := incl (atts_e T relname e) U -> forall ce A B, R A B -> ev ce A e = ev ce B e.
Definition Vc (c : scond T relname) := incl (atts_c T relname c) U ->
  forall ce A B, R A B -> ec ce A c = ec ce B c /\ er ce A c = er ce B c.
Definition Vq (q : squery T relname) := incl (atts_q T relname q) U -> forall ce A B, R A B -> eq_ ce A q = eq_ ce B q.
Definition Vs (sp : sspec T relname) := incl (atts_s T relname sp) U ->
  forall ce A B ex, R A B -> RL (es ce A sp ex) (es ce B sp ex).
Definition Vf (f : sfrom T relname) := incl (atts_f T relname f) U -> forall ce A B, R A B -> ef ce A f = ef ce B f.

Lemma incl_flat_map_inv : forall (X : Type) (f : X -> list (Tuple.attribute T)) l, incl (flat_map f l) U ->
  forall x, In x l -> incl (f x) U.
Proof. intros X f l H x Hx a Ha; apply H, in_flat_map; exists x; tauto. Qed.

Lemma existsb_ext_in : forall (X : Type) (f g : X -> bool) l, (forall x, In x l -> f x = g x) -> existsb f l = existsb g l.
Proof. intros X f g l H; induction l as [ | x l IH]; [reflexivity | simpl; rewrite H, IH; [reflexivity | | left]; auto]. intros; apply H; right; assumption. Qed.

Ltac split_incl :=
  repeat match goal with
         | H : incl (_ ++ _) U |- _ => apply incl_app_inv in H; destruct H
         end.

Ltac prep_s :=
  intros; cbn [atts_e atts_c atts_q atts_s atts_f] in *;
  fold (atts_e T relname) (atts_c T relname) (atts_q T relname) (atts_s T relname) (atts_f T relname) in *; split_incl;
  repeat match goal with
         | H : incl ?u U -> _, K : incl ?u U |- _ => specialize (H K)
         | H : (forall ce A B, _ -> _ /\ _) |- _ =>
           let H1 := fresh "IH1" in let H2 := fresh "IH2" in
           assert (H1 := fun ce A B r => proj1 (H ce A B r)); assert (H2 := fun ce A B r => proj2 (H ce A B r)); clear H
         | H : forall y, In y ?l -> incl _ U -> _, K : incl (flat_map _ ?l) U |- _ =>
           let H' := fresh "IHl" in pose proof (fun y Hy => H y Hy (incl_flat_map_inv _ _ _ K y Hy)) as H'; clear H
         | H : forall e d n, In (O_By e d n) ?l -> incl _ U -> _, K : incl (flat_map _ ?l) U |- _ =>
           let H' := fresh "IHo" in pose proof (fun e d n Hy => H e d n Hy (incl_flat_map_inv _ _ _ K _ Hy)) as H'; clear H
         | H : forall e a, In (S_As e a) ?l -> incl _ U -> _, K : incl (flat_map _ ?l) U |- _ =>
           let H' := fresh "IHs" in pose proof (fun e a Hy => H e a Hy (incl_flat_map_inv _ _ _ K _ Hy)) as H'; clear H
         | H : forall l, In l ?ss -> forall y, In y l -> incl _ U -> _, K : incl (flat_map (flat_map _) ?ss) U |- _ =>
           let H' := fresh "IHg" in
           pose proof (fun l Hl y Hy => H l Hl y Hy (incl_flat_map_inv _ _ _ (incl_flat_map_inv _ _ _ K l Hl) y Hy)) as H'; clear H
         end.

Ltac rel := first [ assumption | apply R_Rq; rel | apply R_cons; rel | apply Rq_cons; rel | apply R_base ].

Ltac leaf :=
  match goal with
  | H : forall ce A B, _ -> ?f ce A ?x = ?f ce B ?x |- ?f _ _ ?x = ?f _ _ ?x => apply H; rel
  | H : forall ce A B ex, _ -> ?f ce A ?x ex = ?f ce B ?x ex |- ?f _ _ ?x _ = ?f _ _ ?x _ => apply H; rel
  | H : forall y, In y ?l -> forall ce A B, _ -> ?f ce A y = ?f ce B y, Hy : In ?x ?l |- ?f _ _ ?x = ?f _ _ ?x =>
    apply (H x Hy); rel
  | H : forall e d n, In (O_By e d n) ?l -> forall ce A B, _ -> ?f ce A e = ?f ce B e, Hy : In (O_By ?x ?d ?n) ?l
    |- ?f _ _ ?x = ?f _ _ ?x => apply (H x d n Hy); rel
  | H : forall e a, In (S_As e a) ?l -> forall ce A B, _ -> ?f ce A e = ?f ce B e, Hy : In (S_As ?x ?a) ?l
    |- ?f _ _ ?x = ?f _ _ ?x => apply (H x a Hy); rel
  | H : forall l, In l ?ss -> forall y, In y l -> forall ce A B, _ -> ?f ce A y = ?f ce B y, Hl : In ?l ?ss, Hy : In ?x ?l
    |- ?f _ _ ?x = ?f _ _ ?x => apply (H l Hl x Hy); rel
  | |- is_hidden _ _ = is_hidden _ _ => apply is_hidden_R; rel
  | |- lookup _ ?a = lookup _ ?a =>
    apply lookup_R; [rel | match goal with K : incl ?l U |- _ => apply K; simpl; tauto end]
  end.

Ltac scong :=
  repeat (first [ reflexivity
                | leaf
                | match goal with |- map _ ?l = map _ ?l => apply map_ext_in; intros ? ? end
                | match goal with |- flat_map _ ?l = flat_map _ ?l => apply flat_map_ext_in; intros ? ? end
                | match goal with |- filter _ ?l = filter _ ?l => apply filter_ext_in; intros ? ? end
                | match goal with |- existsb _ ?l = existsb _ ?l => apply existsb_ext_in; intros ? ? end
                | match goal with |- ?L = ?R =>
                    lazymatch L with context [match ?a with _ => _ end] =>
                      lazymatch R with context [match ?b with _ => _ end] =>
                        first [ constr_eq a b; destruct a
                              | let E := fresh "E" in assert (E : a = b) by scong; rewrite E; destruct b ] end end end
                | match goal with |- (fun _ => _) = (fun _ => _) => let t := fresh "t" in extensionality t end
                | f_equal ]).

Ltac unf := cbn [eval_sexpr eval_scond scond_raises eval_squery eval_sspec eval_sfrom
                 atts_e atts_c atts_q atts_s atts_f] in *;
  fold ev ec er eq_ es ef (atts_e T relname) (atts_c T relname) (atts_q T relname) (atts_s T relname)
       (atts_f T relname) in *.

Ltac open_v := unfold Ve, Vc, Vq, Vs, Vf, LE, LO; cbv beta.

Lemma v_const : forall v, Ve (E_Const T relname v).
Proof. open_v; prep_s; unf; scong. Qed.

Lemma v_col : forall a, Ve (E_Col T relname a).
Proof. open_v; prep_s; unf; scong. Qed.

Lemma v_fun : forall f l, LE T relname Ve l -> Ve (E_Fun f l).
Proof. open_v; prep_s; unf; scong. Qed.

Lemma v_agg : forall ag sq e c, Ve e -> Vc c -> Ve (E_Agg ag sq e c).
Proof.
open_v; prep_s; unf; match goal with HR : R _ _ |- _ => rename HR into H5 end.
assert (Hc : incl (sexpr_cols ORN basesort ce e ++ scond_cols ORN basesort ce c) U).
{ apply incl_app; eapply incl_tran; [apply cols_atts_e | assumption | apply cols_atts_c | assumption]. }
rewrite (is_hidden_R A B (E_Agg ag sq e c) H5); destruct (is_hidden B _); [reflexivity | ].
generalize (agg_env_R _ A B Hc H5); generalize (agg_env (sexpr_cols ORN basesort ce e ++ scond_cols ORN basesort ce c) A)
  (agg_env (sexpr_cols ORN basesort ce e ++ scond_cols ORN basesort ce c) B); intros X Y HXY.
destruct HXY as [[[sa g] h] | [[sa g] h] X Y HXY]; scong.
Qed.

Lemma v_aggx : forall ag sq e sep lo c, Ve e -> (forall s, sep = Some s -> Ve s) -> LO T relname Ve lo -> Vc c ->
  Ve (E_AggX ag sq e sep lo c).
Proof.
open_v; intros ag sq e sep lo c He Hs Ho Hc0.
destruct sep as [s0 | ]; [specialize (Hs s0 eq_refl) | clear Hs]; prep_s; unf;
  match goal with HR : R _ _ |- _ => rename HR into H5 end.
all: match goal with |- context [agg_env ?cols ?A] =>
       assert (Hc : incl cols U) by
         (repeat apply incl_app; try (eapply incl_tran; [apply cols_atts_e | assumption]);
          try (eapply incl_tran; [apply cols_atts_c | assumption]); try (intros ? []);
          intros x Hx; apply in_flat_map in Hx; destruct Hx as [[y d n] [Hy Hx]];
          apply (incl_flat_map_inv _ _ _ ltac:(eassumption) _ Hy); exact (cols_atts_e _ _ _ _ y ce x Hx)) end.
all: match type of H5 with R ?A ?B => rewrite (is_hidden_R A B _ H5); destruct (is_hidden B _); [reflexivity | ];
       match goal with |- context [agg_env ?cols A] =>
         generalize (agg_env_R cols A B Hc H5); generalize (agg_env cols A) (agg_env cols B); intros X Y HXY end end.
all: destruct HXY as [[[sa g] h] | [[sa g] h] X Y HXY]; scong.
Qed.

Lemma v_case : forall c e1 e2, Vc c -> Ve e1 -> Ve e2 -> Ve (E_Case c e1 e2).
Proof. open_v; prep_s; unf; scong. Qed.

Lemma v_cond : forall c, Vc c -> Ve (E_Cond c).
Proof. open_v; prep_s; unf; scong. Qed.

Lemma v_sub : forall q, Vq q -> Ve (E_Sub q).
Proof. open_v; prep_s; unf; scong. Qed.

Lemma v_grouping : forall x, Ve x -> Ve (E_Grouping x).
Proof. open_v; prep_s; unf; match goal with HR : R ?A ?B |- _ => destruct HR end; reflexivity. Qed.

Lemma v_conj : forall a c1 c2, Vc c1 -> Vc c2 -> Vc (C_Conj a c1 c2).
Proof. open_v; prep_s; unf; split; scong. Qed.

Lemma v_not : forall c, Vc c -> Vc (C_Not c).
Proof. open_v; prep_s; unf; split; scong. Qed.

Lemma v_true : Vc (C_True T relname).
Proof. open_v; intros; split; reflexivity. Qed.

Lemma v_pred : forall p l, LE T relname Ve l -> Vc (C_Pred p l).
Proof. open_v; prep_s; unf; split; scong. Qed.

Lemma v_expr : forall e, Ve e -> Vc (C_Expr e).
Proof. open_v; prep_s; unf; split; scong. Qed.

Lemma v_quant : forall qtf p l q la, LE T relname Ve l -> Vq q -> Vc (C_Quant qtf p l q la).
Proof. open_v; prep_s; unf; split; scong. Qed.

Lemma v_in : forall l q la, LE T relname Ve l -> Vq q -> Vc (C_In l q la).
Proof. open_v; prep_s; unf; split; scong. Qed.

Lemma v_exists : forall q, Vq q -> Vc (C_Exists q).
Proof. open_v; prep_s; unf; split; scong. Qed.

(** ** Lists of rows with their environments *)

Lemma RL_fst : forall l1 l2, RL l1 l2 -> map (@fst _ _) l1 = map (@fst _ _) l2.
Proof. intros l1 l2 H; induction H as [ | x y l1 l2 [E _] H IH]; simpl; [reflexivity | rewrite E, IH; reflexivity]. Qed.

Lemma RL_dedup_rec : forall seen l1 l2, RL l1 l2 ->
  RL (dedup_rec O (@fst _ _) seen l1) (dedup_rec O (@fst _ _) seen l2).
Proof.
intros seen l1 l2 H; revert seen; induction H as [ | x y l1 l2 [E K] H IH]; intro seen; simpl; [constructor | ].
rewrite E; destruct (tuple_mem O (fst y) seen); [apply IH | constructor; [split; assumption | apply IH]].
Qed.

Lemma RL_dedup : forall l1 l2, RL l1 l2 -> RL (dedup_on O (@fst _ _) l1) (dedup_on O (@fst _ _) l2).
Proof. intros l1 l2 H; rewrite !dedup_on_rec; apply RL_dedup_rec; exact H. Qed.

Lemma F2_sort_on : forall (X Y : Type) (P : X -> Y -> Prop) specs k1 k2 l1 l2, Forall2 P l1 l2 ->
  (forall x y, P x y -> k1 x = k2 y) -> Forall2 P (sort_on O specs k1 l1) (sort_on O specs k2 l2).
Proof.
intros X Y P specs k1 k2 l1 l2 H K; unfold sort_on, msort.
apply (F2_map2 _ _ P _ _ (fun a b => fst a = fst b /\ P (snd a) (snd b))); [ | intros a b [_ Hab]; exact Hab].
rewrite !map_length, (F2_length _ _ _ _ _ H).
apply F2_msort_fuel; [intros [a1 x1] [b1 y1] [a2 x2] [b2 y2] [E1 _] [E2 _]; simpl in *; rewrite E1, E2; reflexivity | ].
apply (F2_map2 _ _ (fun a b => fst a = fst b /\ P (snd a) (snd b)) X Y P); [exact H | intros x y Hxy; split; [apply K; exact Hxy | exact Hxy]].
Qed.

Lemma F2_offset_limit : forall (X Y : Type) (P : X -> Y -> Prop) off lim l1 l2, Forall2 P l1 l2 ->
  Forall2 P (offset_limit off lim l1) (offset_limit off lim l2).
Proof.
intros X Y P off lim l1 l2 H; unfold offset_limit; destruct off; destruct lim;
  repeat first [apply F2_firstn | apply F2_skipn]; exact H.
Qed.

Notation ordr := (ord_rows T relname ORN basesort instance O).
Notation ordk := (ord_keys T relname ORN basesort instance O).

Lemma ordk_R : forall lo ce x y, (forall e d n, In (O_By e d n) lo -> forall ce A B, R A B -> ev ce A e = ev ce B e) ->
  fst x = fst y -> R (snd x) (snd y) -> ordk ce lo x = ordk ce lo y.
Proof.
intros lo ce x y Ho E H; unfold ord_keys; apply map_ext_in; intros [e d n] Hin; rewrite E.
destruct (is_output_col (fst y) e); [reflexivity | apply (Ho e d n Hin); exact H].
Qed.

Lemma ordr_RL : forall q lo ce A B, R A B -> (forall ce A B, R A B -> eq_ ce A q = eq_ ce B q) ->
  (forall sp, q = SQ_Select sp -> forall ce A B ex, R A B -> RL (es ce A sp ex) (es ce B sp ex)) ->
  RL (ordr ce A q lo) (ordr ce B q lo).
Proof.
intros q lo ce A B HR Hq Hs.
assert (M : RL (map (fun t => (t, slice_t T relname t :: A)) (eq_ ce A q)) (map (fun t => (t, slice_t T relname t :: B)) (eq_ ce B q))).
{ rewrite (Hq ce A B HR); apply F2_map; intros t _; split; [reflexivity | apply R_cons; exact HR]. }
unfold ord_rows; destruct q; try exact M.
apply (Hs s eq_refl); exact HR.
Qed.

Lemma flag_RL : forall lo ce l1 l2, (forall e d n, In (O_By e d n) lo -> forall ce A B, R A B -> ev ce A e = ev ce B e) ->
  RL l1 l2 -> RL (flag_rows T relname O (ordk ce lo) l1) (flag_rows T relname O (ordk ce lo) l2).
Proof.
intros lo ce l1 l2 Ho H; unfold flag_rows; apply (F2_map2 _ _ _ _ _ _ _ _ _ _ H).
intros x y [E K]; rewrite (ordk_R lo ce x y Ho E K), E; destruct (existsb _ _); split; trivial.
Qed.

Lemma v_table : forall r, Vq (SQ_Table T r).
Proof. open_v; intros; reflexivity. Qed.

Lemma v_set : forall o sq q1 q2, Vq q1 -> Vq q2 -> Vq (SQ_Set o sq q1 q2).
Proof. open_v; prep_s; unf; scong. Qed.

Lemma v_select : forall sp, Vs sp -> Vq (SQ_Select sp).
Proof. open_v; prep_s; unf; apply RL_fst; match goal with H : forall ce A B ex, _ |- _ => apply H; assumption end. Qed.

Lemma v_order : forall q lo off lim, Vq q -> (forall sp, q = SQ_Select sp -> Vs sp) -> LO T relname Ve lo ->
  Vq (SQ_Order q lo off lim).
Proof.
open_v; intros q lo off lim Hq Hs Ho Hi ce A B HR.
cbn [atts_q] in Hi; fold (atts_q T relname) (atts_e T relname) in Hi; apply incl_app_inv in Hi; destruct Hi as [Hi1 Hi2].
specialize (Hq Hi1).
assert (Ho' := fun e d n Hy => Ho e d n Hy (incl_flat_map_inv _ _ _ Hi2 _ Hy)).
assert (Hs' : forall sp, q = SQ_Select sp -> forall ce A B ex, R A B -> RL (es ce A sp ex) (es ce B sp ex))
  by (intros sp E; subst q; apply (Hs sp eq_refl); exact Hi1).
rewrite !eval_order; cbv zeta.
assert (K := flag_RL lo ce _ _ Ho' (ordr_RL q lo ce A B HR Hq Hs')).
f_equal; [ | apply RL_fst; exact K].
apply RL_fst, F2_offset_limit, F2_sort_on; [exact K | intros x y [E H]; exact (ordk_R lo ce x y Ho' E H)].
Qed.

Lemma F2_rev' : forall (X Y : Type) (P : X -> Y -> Prop) l1 l2, Forall2 P l1 l2 -> Forall2 P (rev' l1) (rev' l2).
Proof.
intros X Y P l1 l2 H; unfold rev'; rewrite <- !rev_alt.
induction H; simpl; [constructor | apply F2_app; [exact IHForall2 | constructor; [assumption | constructor]]].
Qed.

Lemma F2_take : forall (c1 c2 : Tuple.tuple T * senv -> comparison) l1 l2, RL l1 l2 ->
  (forall x y, fst x = fst y -> R (snd x) (snd y) -> c1 x = c2 y) ->
  RL ((fix take (l : list (Tuple.tuple T * senv)) : list (Tuple.tuple T * senv) :=
         match l with x :: l' => match c1 x with Eq => x :: take l' | _ => nil end | nil => nil end) l1)
     ((fix take (l : list (Tuple.tuple T * senv)) : list (Tuple.tuple T * senv) :=
         match l with x :: l' => match c2 x with Eq => x :: take l' | _ => nil end | nil => nil end) l2).
Proof.
intros c1 c2 l1 l2 H K; induction H as [ | x y l1 l2 [E Hr] H IH]; [constructor | ].
rewrite (K x y E Hr); destruct (c2 y); try constructor; trivial; split; assumption.
Qed.

Lemma fetch_RL : forall lo off ties pct n (keys : Tuple.tuple T * senv -> list (Tuple.value T)) l1 l2, RL l1 l2 ->
  (forall x y, fst x = fst y -> R (snd x) (snd y) -> keys x = keys y) ->
  fetch_rest T relname O lo off ties pct n keys l1 = fetch_rest T relname O lo off ties pct n keys l2.
Proof.
intros lo off ties pct n keys l1 l2 H K; unfold fetch_rest; cbv zeta.
assert (S := F2_sort_on _ _ _ (map (@sorder_spec T relname) lo) keys keys l1 l2 H (fun x y Hxy => K x y (proj1 Hxy) (proj2 Hxy))).
assert (L := F2_length _ _ _ _ _ S).
assert (Af : RL (match off with Some k => skipn (N.to_nat k) (sort_on O (map (@sorder_spec T relname) lo) keys l1)
                 | None => sort_on O (map (@sorder_spec T relname) lo) keys l1 end)
                (match off with Some k => skipn (N.to_nat k) (sort_on O (map (@sorder_spec T relname) lo) keys l2)
                 | None => sort_on O (map (@sorder_spec T relname) lo) keys l2 end))
  by (destruct off; [apply F2_skipn | ]; exact S).
rewrite L.
match goal with |- keep_errors O (map _ (?F1 ++ ?E1)) _ = keep_errors O (map _ (?F2 ++ ?E2)) _ =>
  assert (Fi : RL F1 F2) by (apply F2_firstn; exact Af);
  assert (Ex : RL E1 E2) end.
- destruct ties; [ | constructor].
  assert (Rv := F2_rev' _ _ _ _ _ Fi); destruct Rv as [ | x y r1 r2 [E Hr] _]; [constructor | ].
  apply F2_take; [apply F2_skipn; exact Af | ].
  intros a b Ea Ra; rewrite (K x y E Hr), (K a b Ea Ra); reflexivity.
- f_equal; apply RL_fst; [apply F2_app; assumption | exact H].
Qed.

Lemma v_fetch : forall q lo off ties pct n, Vq q -> (forall sp, q = SQ_Select sp -> Vs sp) -> LO T relname Ve lo ->
  Vq (SQ_Fetch q lo off ties pct n).
Proof.
open_v; intros q lo off ties pct n Hq Hs Ho Hi ce A B HR.
cbn [atts_q] in Hi; fold (atts_q T relname) (atts_e T relname) in Hi; apply incl_app_inv in Hi; destruct Hi as [Hi1 Hi2].
specialize (Hq Hi1).
assert (Ho' := fun e d n Hy => Ho e d n Hy (incl_flat_map_inv _ _ _ Hi2 _ Hy)).
assert (Hs' : forall sp, q = SQ_Select sp -> forall ce A B ex, R A B -> RL (es ce A sp ex) (es ce B sp ex))
  by (intros sp E; subst q; apply (Hs sp eq_refl); exact Hi1).
rewrite !eval_fetch; apply fetch_RL; [ | intros x y E K; exact (ordk_R lo ce x y Ho' E K)].
exact (flag_RL lo ce _ _ Ho' (ordr_RL q lo ce A B HR Hq Hs')).
Qed.

Lemma v_window : forall q lw, Vq q ->
  (forall f lp lo a, In (W_As f lp lo a) lw -> LE T relname Ve lp /\ LO T relname Ve lo /\ LE T relname Ve (wexprs T relname f)) ->
  Vq (SQ_Window q lw).
Proof.
open_v; intros q lw Hq Hw Hi ce A B HR.
cbn [atts_q] in Hi; fold (atts_q T relname) (atts_e T relname) in Hi; apply incl_app_inv in Hi; destruct Hi as [Hi1 Hi2].
rewrite !eval_windows; f_equal; [ | apply Hq; assumption].
apply map_ext_in; intros [f lp lo a] Iw.
destruct (Hw f lp lo a Iw) as [Hp [Ho Hf]]; clear Hw.
assert (Kw := incl_flat_map_inv _ _ _ Hi2 _ Iw); cbv beta iota in Kw.
apply incl_app_inv in Kw; destruct Kw as [Kp Kw]; apply incl_app_inv in Kw; destruct Kw as [Ko Kf].
assert (Hfe : forall y, In y (wexprs T relname f) -> incl (atts_e T relname y) U).
{ clear - Kf; revert Kf; induction f; intros Kf y Hy; cbn [wexprs] in Hy; try contradiction;
    try (destruct Hy as [<- | []]; exact Kf);
    try (apply incl_app_inv in Kf; destruct Kf as [K1 K2]; destruct Hy as [<- | [<- | []]]; assumption).
  exact (IHf Kf y Hy). }
assert (IHp : forall y, In y lp -> forall ce A B, R A B -> ev ce A y = ev ce B y)
  by (intros y Hy; apply (Hp y Hy); exact (incl_flat_map_inv _ _ _ Kp y Hy)).
assert (IHo : forall e d n, In (O_By e d n) lo -> forall ce A B, R A B -> ev ce A e = ev ce B e)
  by (intros e d n Hy; apply (Ho e d n Hy); exact (incl_flat_map_inv _ _ _ Ko _ Hy)).
assert (IHf : forall y, In y (wexprs T relname f) -> forall ce A B, R A B -> ev ce A y = ev ce B y)
  by (intros y Hy; apply (Hf y Hy); exact (Hfe y Hy)).
unfold wfun; extensionality rows.
rewrite (wcomp_ext T relname (fun e t => ev ce (slice_t T relname t :: A) e) (fun e t => ev ce (slice_t T relname t :: B) e) f)
  by (intros e He; extensionality t; apply IHf; [exact He | apply R_cons; exact HR]).
scong.
Qed.

Lemma v_with : forall r q1 q2, Vq q1 -> Vq q2 -> Vq (SQ_With r q1 q2).
Proof.
open_v; prep_s; unf.
match goal with HR : R ?A ?B, H1 : forall ce A B, R A B -> eq_ ce A q1 = eq_ ce B q1 |- _ => rewrite (H1 _ A B HR) end.
match goal with H2 : forall ce A B, R A B -> eq_ ce A q2 = eq_ ce B q2 |- _ => apply H2; assumption end.
Qed.

Lemma v_withrec : forall sq r q1 q2 q3, Vq q1 -> Vq q2 -> Vq q3 -> Vq (SQ_WithRec sq r q1 q2 q3).
Proof.
open_v; prep_s; unf; cbv zeta.
match goal with HR : R ?A ?B, H1 : forall ce A B, R A B -> eq_ ce A q1 = eq_ ce B q1 |- _ => rewrite !(H1 _ A B HR) end.
match goal with HR : R ?A ?B, H2 : forall ce A B, R A B -> eq_ ce A q2 = eq_ ce B q2 |- _ =>
  assert (S : forall r sa, (fun work => eq_ ((r, (sa, work)) :: ce) A q2) = (fun work => eq_ ((r, (sa, work)) :: ce) B q2))
    by (intros; extensionality work; apply H2; exact HR); rewrite S end.
match goal with H3 : forall ce A B, R A B -> eq_ ce A q3 = eq_ ce B q3 |- _ => apply H3; assumption end.
Qed.

Lemma v_fquery : forall q rho, Vq q -> Vf (Fr_Query q rho).
Proof. open_v; prep_s; unf; scong. Qed.

Lemma v_fjoin : forall jt lat f1 f2 c, Vf f1 -> Vf f2 -> Vc c -> Vf (Fr_Join jt lat f1 f2 c).
Proof. open_v; prep_s; unf; cbv zeta; scong. Qed.

Lemma v_ffun : forall name args ord atts, LE T relname Ve args -> Vf (Fr_Fun name args ord atts).
Proof.
open_v; prep_s; unf; cbv zeta.
match goal with HR : R ?A ?B |- _ =>
  assert (M : map (ev ce A) args = map (ev ce B) args) by (apply map_ext_in; intros; apply IHl; assumption); rewrite M end.
reflexivity.
Qed.

Lemma select_rest_RL : forall s h sa sq gs ce A B, R A B ->
  match s with S_Star _ _ => True | S_List l => forall e a, In (S_As e a) l -> forall ce A B, R A B -> ev ce A e = ev ce B e end ->
  (forall ce A B, R A B -> ec ce A h = ec ce B h) -> (forall ce A B, R A B -> er ce A h = er ce B h) ->
  RL (select_rest ORN O basesort instance ce A sa sq s h gs) (select_rest ORN O basesort instance ce B sa sq s h gs).
Proof.
intros s h sa sq gs ce A B HR Hs Ec Rc; unfold select_rest; cbv zeta.
destruct sq; [ | apply RL_dedup]; unfold RL.
all: apply (F2_map2 _ _ _ _ _ (fun x y => R (fst x) (fst y) /\ snd x = snd y)).
2, 4: intros x y [Hxy E]; simpl; rewrite E; split; [ | exact Hxy];
      destruct s as [ | l];
      [ destruct (R_head _ _ Hxy) as [s0 [X' [Y' [E1 E2]]]]; rewrite E1, E2; reflexivity
      | destruct (snd y); [f_equal | ]; f_equal; apply map_ext_in; intros [e a] Hea; rewrite (Hs e a Hea ce _ _ Hxy); reflexivity ].
all: apply F2_filter; [ | intros x y [Hxy E]; rewrite E, (Ec ce _ _ Hxy); reflexivity].
all: apply (F2_map2 _ _ _ _ _ R); [ | intros x y Hxy; split; [exact Hxy | simpl; rewrite (Rc ce x y Hxy);
       destruct (R_head _ _ Hxy) as [s0 [X' [Y' [E1 E2]]]]; rewrite E1, E2; reflexivity]].
all: apply F2_map; intros; apply R_cons; exact HR.
Qed.

Definition gR (g : sgroup T relname) : Prop :=
  match g with
  | G_Fine _ _ => True
  | G_By l | G_Rollup l | G_Cube l => forall y, In y l -> forall ce A B, R A B -> ev ce A y = ev ce B y
  | G_Sets ss => forall l, In l ss -> forall y, In y l -> forall ce A B, R A B -> ev ce A y = ev ce B y
  end.

Lemma gk_R : forall g ce A B, gR g -> R A B ->
  gkeys_of ORN O basesort instance ce A g = gkeys_of ORN O basesort instance ce B g /\
  row_vals_of ORN O basesort instance ce A g = row_vals_of ORN O basesort instance ce B g.
Proof.
intros g ce A B Hg HAB; split; extensionality t; destruct g as [ | l | ss | l | l]; simpl in Hg;
  unfold gkeys_of, row_vals_of; try reflexivity;
  try (apply map_ext_in; intros y Hy; apply (Hg y Hy); apply R_cons; exact HAB).
all: revert Hg; induction ss as [ | l0 ss IH]; intro Hg; [reflexivity | ]; cbn; f_equal;
  [apply map_ext_in; intros y Hy; apply (Hg l0 (or_introl eq_refl) y Hy); apply R_cons; exact HAB
  | apply IH; intros l1 Hl1; apply Hg; right; exact Hl1].
Qed.

Lemma v_spec : forall sq s lf w g h,
  match s with S_Star _ _ => True | S_List l => forall e a, In (S_As e a) l -> Ve e end ->
  (forall f, In f lf -> Vf f) -> Vc w ->
  match g with
  | G_Fine _ _ => True
  | G_By l | G_Rollup l | G_Cube l => LE T relname Ve l
  | G_Sets ss => forall l, In l ss -> LE T relname Ve l
  end -> Vc h -> Vs (Select sq s lf w g h).
Proof.
open_v; intros sq s lf w g h Hs Hf Hw Hg Hh Hi ce A B ex HAB.
cbn [atts_s] in Hi; fold (atts_e T relname) (atts_c T relname) (atts_f T relname) in Hi.
apply incl_app_inv in Hi; destruct Hi as [Is Hi]; apply incl_app_inv in Hi; destruct Hi as [If Hi].
apply incl_app_inv in Hi; destruct Hi as [Iw Hi]; apply incl_app_inv in Hi; destruct Hi as [Ig Ih].
specialize (Hw Iw); specialize (Hh Ih).
assert (Ec := fun ce A B r => proj1 (Hw ce A B r)); assert (Rc := fun ce A B r => proj2 (Hw ce A B r)).
assert (Ec0 := fun ce A B r => proj1 (Hh ce A B r)); assert (Rc0 := fun ce A B r => proj2 (Hh ce A B r)).
assert (IHf : forall y, In y lf -> forall ce A B, R A B -> ef ce A y = ef ce B y)
  by (intros y Hy; apply (Hf y Hy); exact (incl_flat_map_inv _ _ _ If y Hy)).
assert (Hs' : match s with S_Star _ _ => True
              | S_List l => forall e a, In (S_As e a) l -> forall ce A B, R A B -> ev ce A e = ev ce B e end).
{ destruct s as [ | l]; [exact I | ]; intros e a Hea; apply (Hs e a Hea); exact (incl_flat_map_inv _ _ _ Is _ Hea). }
assert (Hg' : gR g).
{ destruct g as [ | l | ss | l | l]; simpl; trivial;
    try (intros y Hy; apply (Hg y Hy); exact (incl_flat_map_inv _ _ _ Ig y Hy)).
  intros l Hl y Hy; apply (Hg l Hl y Hy); exact (incl_flat_map_inv _ _ _ (incl_flat_map_inv _ _ _ Ig l Hl) y Hy). }
clear Hs Hf Hw Hg Hh.
rewrite !eval_select; cbv zeta.
assert (W : where_rows ORN O basesort instance ce A lf w = where_rows ORN O basesort instance ce B lf w)
  by (unfold where_rows; scong).
destruct (gk_R g ce A B Hg' HAB) as [GK RV].
rewrite W, GK, RV; apply select_rest_RL; trivial.
Qed.

(** * The theorem *)

Theorem scope_query : forall q, incl (atts_q T relname q) U -> forall ce A B, R A B -> eq_ ce A q = eq_ ce B q.
Proof.
intro q; exact (ind_q T relname Ve Vc Vq Vs Vf v_const v_col v_fun v_agg v_aggx v_case v_cond v_sub v_grouping
                  v_conj v_not v_true v_pred v_expr v_quant v_in v_exists v_table v_set v_select v_order v_fetch
                  v_window v_with v_withrec v_spec v_fquery v_fjoin v_ffun q).
Qed.

(** a query in a block depends on the enclosing blocks only through the columns which it names: its evaluation
    in [s :: env1] and in [s :: env2] is the same when [env1] and [env2] bind none of them *)
Corollary scope_block : forall q s ce, incl (atts_q T relname q) U -> eq_ ce (s :: env1) q = eq_ ce (s :: env2) q.
Proof. intros q s ce H; apply scope_query; [exact H | apply R_base]. Qed.

End Scope.









