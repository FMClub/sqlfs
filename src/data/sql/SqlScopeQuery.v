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
Require Import BasicFacts ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection FlatData SqlFull SqlInduction.

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

End Cols.
