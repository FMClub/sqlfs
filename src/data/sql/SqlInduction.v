(** * An induction principle for the queries of [SqlFull.v]

    The syntax is a mutual inductive type with nested lists (the arguments of a function, the items of a
    SELECT, the FROM items, the grouping sets, the sort keys, the window functions). [syn_ind_q] gives, for
    each construct, the hypotheses of induction on its sub-expressions, sub-conditions, sub-queries, blocks
    and FROM items, those of the lists as membership. A proof by this principle is an ordinary proof: the
    recursion is checked once, here, on a small term (a large mutual [Fixpoint] proof is slow to check). *)
Require Import List.
Require Import FlatData SqlFull.

Section Ind.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.

Notation sexpr := (sexpr T relname).
Notation scond := (scond T relname).
Notation squery := (squery T relname).
Notation sspec := (sspec T relname).
Notation sfrom := (sfrom T relname).
Notation swfun := (swfun T relname).

Variables (Pe : sexpr -> Prop) (Pc : scond -> Prop) (Pq : squery -> Prop) (Ps : sspec -> Prop) (Pf : sfrom -> Prop).

(** the expressions of a window function *)
Fixpoint wexprs (f : swfun) : list sexpr :=
  match f with
  | W_Agg _ _ e _ | W_First_Value e _ | W_Last_Value e _ | W_Nth_Value e _ _ => e :: nil
  | W_Lag e _ d | W_Lead e _ d => e :: d :: nil
  | W_Opts f' _ _ => wexprs f'
  | _ => nil
  end.

Definition LE (l : list sexpr) := forall y, In y l -> Pe y.
Definition LO (lo : list (sorder T relname)) := forall e d n, In (O_By e d n) lo -> Pe e.

Hypotheses
  (H_Const : forall v, Pe (E_Const T relname v))
  (H_Col : forall a, Pe (E_Col T relname a))
  (H_Fun : forall f l, LE l -> Pe (E_Fun f l))
  (H_Agg : forall ag sq e c, Pe e -> Pc c -> Pe (E_Agg ag sq e c))
  (H_AggX : forall ag sq e sep lo c, Pe e -> (forall s, sep = Some s -> Pe s) -> LO lo -> Pc c ->
                                    Pe (E_AggX ag sq e sep lo c))
  (H_Case : forall c e1 e2, Pc c -> Pe e1 -> Pe e2 -> Pe (E_Case c e1 e2))
  (H_Cond : forall c, Pc c -> Pe (E_Cond c))
  (H_Sub : forall q, Pq q -> Pe (E_Sub q))
  (H_Grouping : forall x, Pe x -> Pe (E_Grouping x))
  (H_Conj : forall a c1 c2, Pc c1 -> Pc c2 -> Pc (C_Conj a c1 c2))
  (H_Not : forall c, Pc c -> Pc (C_Not c))
  (H_True : Pc (C_True T relname))
  (H_Pred : forall p l, LE l -> Pc (C_Pred p l))
  (H_Expr : forall e, Pe e -> Pc (C_Expr e))
  (H_Quant : forall qtf p l q la, LE l -> Pq q -> Pc (C_Quant qtf p l q la))
  (H_In : forall l q la, LE l -> Pq q -> Pc (C_In l q la))
  (H_Exists : forall q, Pq q -> Pc (C_Exists q))
  (H_Table : forall r, Pq (SQ_Table T r))
  (H_Set : forall o sq q1 q2, Pq q1 -> Pq q2 -> Pq (SQ_Set o sq q1 q2))
  (H_Select : forall sp, Ps sp -> Pq (SQ_Select sp))
  (H_Order : forall q lo off lim, Pq q -> (forall sp, q = SQ_Select sp -> Ps sp) -> LO lo -> Pq (SQ_Order q lo off lim))
  (H_Fetch : forall q lo off ties pct n, Pq q -> (forall sp, q = SQ_Select sp -> Ps sp) -> LO lo ->
                                         Pq (SQ_Fetch q lo off ties pct n))
  (H_Window : forall q lw, Pq q ->
                (forall f lp lo a, In (W_As f lp lo a) lw -> LE lp /\ LO lo /\ LE (wexprs f)) ->
                Pq (SQ_Window q lw))
  (H_With : forall r q1 q2, Pq q1 -> Pq q2 -> Pq (SQ_With r q1 q2))
  (H_WithRec : forall sq r q1 q2 q3, Pq q1 -> Pq q2 -> Pq q3 -> Pq (SQ_WithRec sq r q1 q2 q3))
  (H_Spec : forall sq s lf w g h,
      match s with S_Star _ _ => True | S_List l => forall e a, In (S_As e a) l -> Pe e end ->
      (forall f, In f lf -> Pf f) -> Pc w ->
      match g with
      | G_Fine _ _ => True
      | G_By l | G_Rollup l | G_Cube l => LE l
      | G_Sets ss => forall l, In l ss -> LE l
      end -> Pc h -> Ps (Select sq s lf w g h))
  (H_FQuery : forall q rho, Pq q -> Pf (Fr_Query q rho))
  (H_FJoin : forall jt lat f1 f2 c, Pf f1 -> Pf f2 -> Pc c -> Pf (Fr_Join jt lat f1 f2 c))
  (H_FFun : forall name args ord atts, LE args -> Pf (Fr_Fun name args ord atts)).

Fixpoint ind_e (e : sexpr) : Pe e
with ind_c (c : scond) : Pc c
with ind_q (q : squery) : Pq q
with ind_s (sp : sspec) : Ps sp
with ind_f (f : sfrom) : Pf f.
Proof.
- destruct e as [v | a | f l | ag sq e c | ag sq e sep lo c | c e1 e2 | c | q | x].
  + apply H_Const.
  + apply H_Col.
  + apply H_Fun; induction l as [ | x l IH]; intros y Hy; [destruct Hy | ].
    destruct Hy as [<- | Hy]; [apply ind_e | exact (IH y Hy)].
  + apply H_Agg; [apply ind_e | apply ind_c].
  + apply H_AggX; [apply ind_e | | | apply ind_c].
    * destruct sep as [s0 | ]; intros s E; [injection E; intros <-; apply ind_e | discriminate].
    * induction lo as [ | [x d' n'] lo IH]; intros y d0 n0 Hy; [destruct Hy | ].
      destruct Hy as [Hy | Hy]; [injection Hy; intros _ _ <-; apply ind_e | exact (IH y d0 n0 Hy)].
  + apply H_Case; [apply ind_c | apply ind_e | apply ind_e].
  + apply H_Cond, ind_c.
  + apply H_Sub, ind_q.
  + apply H_Grouping, ind_e.
- destruct c as [a c1 c2 | c | | p l | e | qtf p l q la | l q la | q].
  + apply H_Conj; apply ind_c.
  + apply H_Not, ind_c.
  + apply H_True.
  + apply H_Pred; induction l as [ | x l IH]; intros y Hy; [destruct Hy | ].
    destruct Hy as [<- | Hy]; [apply ind_e | exact (IH y Hy)].
  + apply H_Expr, ind_e.
  + apply H_Quant; [ | apply ind_q]; induction l as [ | x l IH]; intros y Hy; [destruct Hy | ].
    destruct Hy as [<- | Hy]; [apply ind_e | exact (IH y Hy)].
  + apply H_In; [ | apply ind_q]; induction l as [ | x l IH]; intros y Hy; [destruct Hy | ].
    destruct Hy as [<- | Hy]; [apply ind_e | exact (IH y Hy)].
  + apply H_Exists, ind_q.
- destruct q as [r | o sq q1 q2 | sp | q lo off lim | q lo off ties pct n | q lw | r q1 q2 | sq r q1 q2 q3].
  + apply H_Table.
  + apply H_Set; apply ind_q.
  + apply H_Select, ind_s.
  + apply H_Order; [apply ind_q | | ].
    * destruct q; intros sp E; try discriminate; injection E; intros <-; apply ind_s.
    * induction lo as [ | [x d' n'] lo IH]; intros y d0 n0 Hy; [destruct Hy | ].
      destruct Hy as [Hy | Hy]; [injection Hy; intros _ _ <-; apply ind_e | exact (IH y d0 n0 Hy)].
  + apply H_Fetch; [apply ind_q | | ].
    * destruct q; intros sp E; try discriminate; injection E; intros <-; apply ind_s.
    * induction lo as [ | [x d' n'] lo IH]; intros y d0 n0 Hy; [destruct Hy | ].
      destruct Hy as [Hy | Hy]; [injection Hy; intros _ _ <-; apply ind_e | exact (IH y d0 n0 Hy)].
  + apply H_Window; [apply ind_q | ].
    induction lw as [ | [f lp lo a'] lw IH]; intros f0 lp0 lo0 a0 Hw; [destruct Hw | ].
    destruct Hw as [Hw | Hw]; [ | exact (IH f0 lp0 lo0 a0 Hw)].
    injection Hw; intros _ <- <- <-; split; [ | split].
    * clear IH Hw; induction lp as [ | x l IH]; intros y Hy; [destruct Hy | ].
      destruct Hy as [<- | Hy]; [apply ind_e | exact (IH y Hy)].
    * clear IH Hw; induction lo as [ | [x d' n'] lo IH]; intros y d0 n0 Hy; [destruct Hy | ].
      destruct Hy as [Hy | Hy]; [injection Hy; intros _ _ <-; apply ind_e | exact (IH y d0 n0 Hy)].
    * clear IH Hw; induction f; intros y Hy; simpl in Hy; try contradiction; try exact (IHf y Hy);
        repeat (destruct Hy as [<- | Hy]; [apply ind_e | ]); contradiction.
  + apply H_With; apply ind_q.
  + apply H_WithRec; apply ind_q.
- destruct sp as [sq s lf w g h]; apply H_Spec; [ | | apply ind_c | | apply ind_c].
  + destruct s as [ | l]; [exact I | ].
    induction l as [ | [x a'] l IH]; intros y a Hy; [destruct Hy | ].
    destruct Hy as [Hy | Hy]; [injection Hy; intros _ <-; apply ind_e | exact (IH y a Hy)].
  + induction lf as [ | x l IH]; intros y Hy; [destruct Hy | ].
    destruct Hy as [<- | Hy]; [apply ind_f | exact (IH y Hy)].
  + destruct g as [ | l | ss | l | l]; [exact I | | | | ].
    1, 3, 4: induction l as [ | x l IH]; intros y Hy; [destruct Hy | ];
      destruct Hy as [<- | Hy]; [apply ind_e | exact (IH y Hy)].
    induction ss as [ | l ss IH]; intros l' Hl; [destruct Hl | ].
    destruct Hl as [<- | Hl]; [ | exact (IH l' Hl)].
    clear IH; induction l as [ | x l IH]; intros y Hy; [destruct Hy | ].
    destruct Hy as [<- | Hy]; [apply ind_e | exact (IH y Hy)].
- destruct f as [q rho | jt lat f1 f2 c | name args ord atts].
  + apply H_FQuery, ind_q.
  + apply H_FJoin; [apply ind_f | apply ind_f | apply ind_c].
  + apply H_FFun; induction args as [ | x l IH]; intros y Hy; [destruct Hy | ].
    destruct Hy as [<- | Hy]; [apply ind_e | exact (IH y Hy)].
Qed.

End Ind.
