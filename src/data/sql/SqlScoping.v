(** * Scoping and evaluation (TODO 6.2)

    The scoping condition of [wf_query] (no free column: [squery_cols] is empty) is a condition on the
    evaluation: a column is read from the slice of the block which binds it. [scope_e] and [scope_c]: an
    expression (a condition) without subqueries and aggregates whose columns are all columns of the current
    row has the same value whatever the enclosing blocks are: its evaluation reads nothing outside the row.
    [wf_set_op]: the operands of a well-formed set operation have the same sort, so that the operation is
    evaluated (the evaluation of operands of different sorts is empty). *)
Require Import List Bool String.
Require Import BasicFacts ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection
        FlatData Bool3 Formula SqlFull SqlWellFormed.

Open Scope string_scope.

Section Sec.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.
Hypothesis ORN : Oset.Rcd relname.
Hypothesis O : dialect T.

Import Tuple.

Notation setA := (Fset.set (A T)).
Notation BTupleT := (Fecol.CBag (CTuple T)).
Notation bagT := (Febag.bag BTupleT).

Hypothesis basesort : relname -> setA.
Hypothesis instance : relname -> bagT.

Notation eval_sexpr := (eval_sexpr ORN O basesort instance).
Notation eval_scond := (eval_scond ORN O basesort instance).
Notation eval_squery := (eval_squery ORN O basesort instance).
Notation scond_raises := (scond_raises ORN O basesort instance).
Notation sexpr := (sexpr T relname).
Notation scond := (scond T relname).

(** the expressions and conditions without subqueries, aggregates and window functions *)
Fixpoint simple_e (e : sexpr) : bool :=
  match e with
  | @E_Const _ _ _ | @E_Col _ _ _ => true
  | @E_Fun _ _ _ l => (fix go (l : list sexpr) : bool := match l with nil => true | x :: r => simple_e x && go r end) l
  | @E_Case _ _ c e1 e2 => simple_c c && simple_e e1 && simple_e e2
  | @E_Cond _ _ c => simple_c c
  | _ => false
  end
with simple_c (c : scond) : bool :=
  match c with
  | @C_Conj _ _ _ c1 c2 => simple_c c1 && simple_c c2
  | @C_Not _ _ c => simple_c c
  | @C_True _ _ => true
  | @C_Pred _ _ _ l => (fix go (l : list sexpr) : bool := match l with nil => true | x :: r => simple_e x && go r end) l
  | @C_Expr _ _ e => simple_e e
  | _ => false
  end.

(** the unfoldings of the evaluation which the proofs use *)
Lemma ev_col : forall ce env a, eval_sexpr ce env (E_Col T relname a) =
  if is_hidden env (E_Col T relname a) then null O else lookup env a.
Proof. reflexivity. Qed.
Lemma ev_fun : forall ce env f l, eval_sexpr ce env (E_Fun f l) =
  if is_hidden env (E_Fun f l) then null O
  else let vs := map (eval_sexpr ce env) l in
       match first_error O (if lazy_symbol O f then firstn 1 vs else vs) with
       | Some err => err | None => interp_fun O f vs end.
Proof. reflexivity. Qed.
Lemma ev_case : forall ce env c e1 e2, eval_sexpr ce env (E_Case c e1 e2) =
  if is_hidden env (E_Case c e1 e2) then null O
  else if scond_raises ce env c then error O "error"
  else if is_true3 T (eval_scond ce env c) then eval_sexpr ce env e1 else eval_sexpr ce env e2.
Proof. reflexivity. Qed.
Lemma ev_cond : forall ce env c, eval_sexpr ce env (E_Cond c) =
  if is_hidden env (E_Cond c) then null O
  else if scond_raises ce env c then error O "error" else value_of_truth O (eval_scond ce env c).
Proof. reflexivity. Qed.

Lemma ec_conj : forall ce env a c1 c2,
  eval_scond ce env (C_Conj a c1 c2) = interp_conj (B T) a (eval_scond ce env c1) (eval_scond ce env c2) /\
  scond_raises ce env (C_Conj a c1 c2) =
    (let r1 := scond_raises ce env c1 in
     let r2 := scond_raises ce env c2 in
     let decides x := match a with
                      | And_F => is_true3 T (Bool.negb (B T) (eval_scond ce env x))
                      | Or_F => is_true3 T (eval_scond ce env x)
                      end in
     (r1 && negb (negb r2 && decides c2)) || (r2 && negb (negb r1 && decides c1))).
Proof. split; reflexivity. Qed.
Lemma ec_not : forall ce env c,
  eval_scond ce env (C_Not c) = Bool.negb (B T) (eval_scond ce env c) /\ scond_raises ce env (C_Not c) = scond_raises ce env c.
Proof. split; reflexivity. Qed.
Lemma ec_pred : forall ce env p l,
  eval_scond ce env (C_Pred p l) = interp_pred O p (cmp_coerce O p (map (sexpr_affinity O) l) (map (eval_sexpr ce env) l)) /\
  scond_raises ce env (C_Pred p l) = (existsb (is_error O) (map (eval_sexpr ce env) l) || pred_error O p (map (eval_sexpr ce env) l)).
Proof. split; reflexivity. Qed.
Lemma ec_expr : forall ce env e,
  eval_scond ce env (C_Expr e) = truth_of_value O (eval_sexpr ce env e) /\
  scond_raises ce env (C_Expr e) = (is_error O (eval_sexpr ce env e) || truth_error O (eval_sexpr ce env e)).
Proof. split; reflexivity. Qed.

Section Scope.

Variable ce : cte_env T relname.
Variable sa : setA.
Variable g : list (tuple T).
Variable hid : list sexpr.
Variables env1 env2 : senv T relname.

Notation E1 := ((sa, g, hid) :: env1).
Notation E2 := ((sa, g, hid) :: env2).

Definition bound (l : list (attribute T)) := forall a, In a l -> a inS sa.

Lemma bound_app : forall l1 l2, bound (l1 ++ l2) -> bound l1 /\ bound l2.
Proof. intros l1 l2 H; split; intros a I; apply H; apply in_or_app; [left | right]; exact I. Qed.

Fixpoint scope_e (e : sexpr) {struct e} :
  simple_e e = true -> bound (sexpr_cols ORN basesort ce e) -> eval_sexpr ce E1 e = eval_sexpr ce E2 e
with scope_c (c : scond) {struct c} :
  simple_c c = true -> bound (scond_cols ORN basesort ce c) ->
  eval_scond ce E1 c = eval_scond ce E2 c /\ scond_raises ce E1 c = scond_raises ce E2 c.
Proof.
- destruct e as [v | a | f l | | | c e1 e2 | c | q | x]; intros S B; try discriminate S.
  + reflexivity.
  + assert (K := B a (or_introl eq_refl)); rewrite !ev_col; cbn [lookup is_hidden]; rewrite K; reflexivity.
  + assert (M : map (eval_sexpr ce E1) l = map (eval_sexpr ce E2) l).
    { simpl in S, B; revert S B.
      refine ((fix go (k : list sexpr) :
                 (fix go (l : list sexpr) : bool := match l with nil => true | x :: r => simple_e x && go r end) k
                 = true -> bound (flat_map (sexpr_cols ORN basesort ce) k) ->
                 map (eval_sexpr ce E1) k = map (eval_sexpr ce E2) k := _) l).
      destruct k as [ | x r]; intros S' B'; [reflexivity | ].
      apply andb_true_iff in S'; destruct S' as [Sx Sr]; simpl in B'; apply bound_app in B'.
      cbn [map]; f_equal; [apply scope_e; tauto | apply go; tauto]. }
    rewrite !ev_fun; cbn [is_hidden]; cbv zeta; rewrite M; reflexivity.
  + simpl in S; rewrite !andb_true_iff in S; destruct S as [[Sc S1] S2].
    simpl in B; apply bound_app in B; destruct B as [Bc B']; apply bound_app in B'; destruct B' as [B1 B2].
    destruct (scope_c c Sc Bc) as [K1 K2].
    rewrite !ev_case; cbn [is_hidden]; rewrite K1, K2, (scope_e e1 S1 B1), (scope_e e2 S2 B2); reflexivity.
  + simpl in S, B; destruct (scope_c c S B) as [K1 K2]; rewrite !ev_cond; cbn [is_hidden]; rewrite K1, K2; reflexivity.
- destruct c as [a c1 c2 | c | | p l | e | | | ]; intros S B; try discriminate S.
  + simpl in S; apply andb_true_iff in S; destruct S as [S1 S2]; simpl in B; apply bound_app in B.
    destruct (scope_c c1 S1 (proj1 B)) as [K1 K1']; destruct (scope_c c2 S2 (proj2 B)) as [K2 K2'].
    rewrite (proj1 (ec_conj _ E1 _ _ _)), (proj1 (ec_conj _ E2 _ _ _)), (proj2 (ec_conj _ E1 _ _ _)), (proj2 (ec_conj _ E2 _ _ _)).
    cbv beta zeta; rewrite K1, K1', K2, K2'; split; reflexivity.
  + simpl in S, B; destruct (scope_c c S B) as [K1 K2].
    rewrite (proj1 (ec_not _ E1 _)), (proj1 (ec_not _ E2 _)), (proj2 (ec_not _ E1 _)), (proj2 (ec_not _ E2 _)), K1, K2; split; reflexivity.
  + split; reflexivity.
  + assert (M : map (eval_sexpr ce E1) l = map (eval_sexpr ce E2) l).
    { simpl in S, B; revert S B.
      refine ((fix go (k : list sexpr) :
                 (fix go (l : list sexpr) : bool := match l with nil => true | x :: r => simple_e x && go r end) k
                 = true -> bound (flat_map (sexpr_cols ORN basesort ce) k) ->
                 map (eval_sexpr ce E1) k = map (eval_sexpr ce E2) k := _) l).
      destruct k as [ | x r]; intros S' B'; [reflexivity | ].
      apply andb_true_iff in S'; destruct S' as [Sx Sr]; simpl in B'; apply bound_app in B'.
      cbn [map]; f_equal; [apply scope_e; tauto | apply go; tauto]. }
    rewrite (proj1 (ec_pred _ E1 _ _)), (proj1 (ec_pred _ E2 _ _)), (proj2 (ec_pred _ E1 _ _)), (proj2 (ec_pred _ E2 _ _)), M; split; reflexivity.
  + simpl in S, B.
    rewrite (proj1 (ec_expr _ E1 _)), (proj1 (ec_expr _ E2 _)), (proj2 (ec_expr _ E1 _)), (proj2 (ec_expr _ E2 _)), (scope_e e S B); split; reflexivity.
Qed.

End Scope.

(** a well-formed set operation: its operands have the same sort, and it is evaluated as the operation of
    their rows *)
Theorem wf_set_op :
  forall ce env o sq q1 q2,
    wf_squery T relname ORN basesort ce (SQ_Set o sq q1 q2) = true ->
    eval_squery ce env (SQ_Set o sq q1 q2) =
    unify_rows O ({{{squery_sort ORN basesort ce q1}}})
      (keep_errors O (eval_set_op O o sq (eval_squery ce env q1) (eval_squery ce env q2))
                   (eval_squery ce env q1 ++ eval_squery ce env q2)).
Proof.
intros ce env o sq q1 q2 W; cbn [wf_squery] in W; rewrite !andb_true_iff in W; destruct W as [[E _] _].
change ((if Fset.equal (A T) (squery_sort ORN basesort ce q1) (squery_sort ORN basesort ce q2)
         then unify_rows O ({{{squery_sort ORN basesort ce q1}}})
                (keep_errors O (eval_set_op O o sq (eval_squery ce env q1) (eval_squery ce env q2))
                             (eval_squery ce env q1 ++ eval_squery ce env q2))
         else nil) =
        unify_rows O ({{{squery_sort ORN basesort ce q1}}})
          (keep_errors O (eval_set_op O o sq (eval_squery ce env q1) (eval_squery ce env q2))
                       (eval_squery ce env q1 ++ eval_squery ce env q2))).
rewrite E; reflexivity.
Qed.

End Sec.
