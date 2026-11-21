(** * The selections of [Sql.v] and of [SqlFull.v] agree (TODO 6.1)

    The blocks [SELECT s FROM q WHERE f] of [Sql.v] without grouping, whose [SELECT] list and [WHERE] formula are
    built from function terms and predicates, translate to [SqlFull.v] ([ft_to], [f_to], [s_to]); the two
    semantics give the same bag of rows when the [FROM] query does ([select_agree]). The dialect of [SqlFull.v] is
    the one of the instance: its functions, predicates and literals are those of [T] ([Hfun], [Hpred],
    [Hconst]), it converts nothing before a comparison ([Hcoerce]), no value is a failure ([Herr], [Hpe]: [Sql.v]
    has no errors), and a NULL has no type ([Hnull]: [SqlFull.v] stores a NULL with the type of its column,
    [Sql.v] keeps the value). *)
Require Import List Bool NArith.
Require Import BasicFacts ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection ListPermut ListSort
        FlatData Bool3 Formula Sql SqlFull.

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

End Sec.
