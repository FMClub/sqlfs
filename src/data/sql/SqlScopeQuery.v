(** * Scoping of whole queries (TODO 6.2)

    A query reads the enclosing blocks only through the columns which it names: its evaluation in an
    environment [p ++ env1] and in [p ++ env2] is the same when [env1] and [env2] bind none of the columns
    which occur in the query ([scope_query]); in particular a closed query is evaluated in the same way
    whatever enclosing blocks which do not reuse its column names ([closed_scope]). The condition on names is
    needed: a failed row of an operand of a product has the columns of its operand only ([SqlSorts.v]), and an
    expression of the block over the columns of the other operand then reads them from the enclosing blocks.

    The environments: [R A B] when [A] and [B] are a common non empty prefix followed by [env1] and [env2]
    (the environments of the expressions), [Rq A B] when they are also allowed to be [env1] and [env2]
    themselves (the environments of the queries). *)
Require Import List Bool String NArith FunctionalExtensionality.
Require Import BasicFacts ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection FlatData SqlFull SqlInduction
        SqlCongruence.

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
Definition Vq (q : squery T relname) := incl (atts_q T relname q) U -> forall ce A B, Rq A B -> eq_ ce A q = eq_ ce B q.
Definition Vs (sp : sspec T relname) := incl (atts_s T relname sp) U ->
  forall ce A B ex, Rq A B -> RL (es ce A sp ex) (es ce B sp ex).
Definition Vf (f : sfrom T relname) := incl (atts_f T relname f) U -> forall ce A B, Rq A B -> ef ce A f = ef ce B f.

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

End Scope.



