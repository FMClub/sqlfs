(** * Congruence of the evaluation (TODO 6.2, 6.4)

    The evaluation of a query depends on the dialect only through the interpretations of the functions,
    predicates, aggregates and table functions which the query uses ([squery_uses]), the other fields of the
    record being equal: [eval_congruence]. This is the basis of the refinement between two dialects
    ([Refinement.v]): two dialects which agree on what a query uses give it the same rows. *)
Require Import List Bool String NArith FunctionalExtensionality.
Require Import BasicFacts ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection
        FlatData Bool3 Formula SqlFull.

Section Sec.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.
Hypothesis ORN : Oset.Rcd relname.

Import Tuple.

Notation predicate := (Tuple.predicate T).
Notation symb := (Tuple.symbol T).
Notation aggregate := (Tuple.aggregate T).
Notation value := (Tuple.value T).
Notation setA := (Fset.set (A T)).
Notation BTupleT := (Fecol.CBag (CTuple T)).
Notation bagT := (Febag.bag BTupleT).
Notation bool3 := (Bool.b (B T)).

(** [O1] with other interpretations of the functions, predicates, aggregates and table functions (and other
    lists of the known ones, which only acceptance reads) *)
Definition with_interp (O1 : dialect T)
           (fi : symb -> list value -> value) (pi : predicate -> list value -> bool3)
           (ai : aggregate -> list value -> value)
           (tf : string -> option (list value -> list (list value)))
           (ks : symb -> nat -> bool) (kp : predicate -> bool) (ka : aggregate -> bool) : dialect T :=
  mk_dialect T (is_null O1) (null O1) (truth_of_value O1) (value_of_truth O1) (eq3 O1) (order O1)
             (value_of_Z O1) (rat_of O1) (value_of_rat O1) (canon O1) (nulls_smallest O1)
             ks kp ka (is_error O1) (error O1) (err_attr O1) (lazy_symbol O1) (pred_error O1)
             (scalar_first_row O1) (const_of O1) (truth_error O1) (attr_affinity O1) (cmp_coerce O1)
             (unify_column O1) tf fi pi ai.

Hypothesis O1 : dialect T.
Hypothesis fi : symb -> list value -> value.
Hypothesis pi : predicate -> list value -> bool3.
Hypothesis ai : aggregate -> list value -> value.
Hypothesis tf : string -> option (list value -> list (list value)).
Hypotheses (ks : symb -> nat -> bool) (kp : predicate -> bool) (ka : aggregate -> bool).

Notation O2 := (with_interp O1 fi pi ai tf ks kp ka).

(** the two dialects agree on a construct *)
Definition agree (u : use T) : Prop :=
  match u with
  | U_Feature _ _ => True
  | U_Symbol _ f n => forall l, List.length l = n -> fi f l = interp_fun O1 f l
  | U_Pred _ p => forall l, pi p l = interp_pred O1 p l
  | U_Agg _ a => forall l, ai a l = interp_agg O1 a l
  | U_Table_Fun _ name => tf name = table_fun O1 name
  end.

Definition ok (l : list (use T)) := forall u, In u l -> agree u.

Lemma ok_app : forall l1 l2, ok (l1 ++ l2) -> ok l1 /\ ok l2.
Proof. intros l1 l2 H; split; intros u I; apply H; apply in_or_app; tauto. Qed.
Lemma ok_cons : forall u l, ok (u :: l) -> agree u /\ ok l.
Proof. intros u l H; split; [apply H; left; reflexivity | intros v I; apply H; right; exact I]. Qed.
Lemma ok_flat_map : forall (X : Type) (f : X -> list (use T)) l, ok (flat_map f l) -> forall x, In x l -> ok (f x).
Proof. intros X f l H x I u J; apply H; apply in_flat_map; exists x; tauto. Qed.

Ltac split_ok :=
  cbn [sexpr_uses scond_uses squery_uses sspec_uses sfrom_uses] in *;
  fold (@sexpr_uses T relname) (@scond_uses T relname) (@squery_uses T relname) (@sspec_uses T relname)
       (@sfrom_uses T relname) in *;
  repeat match goal with
         | H : ok (_ ++ _) |- _ => apply ok_app in H; destruct H
         | H : ok (_ :: _) |- _ => apply ok_cons in H; destruct H
         | H : ok nil |- _ => clear H
         end;
  cbn [agree] in *.

Hypothesis basesort : relname -> setA.
Hypothesis instance : relname -> bagT.

Notation ev2 := (eval_sexpr ORN O2 basesort instance).
Notation ev1 := (eval_sexpr ORN O1 basesort instance).
Notation ec2 := (eval_scond ORN O2 basesort instance).
Notation ec1 := (eval_scond ORN O1 basesort instance).
Notation er2 := (scond_raises ORN O2 basesort instance).
Notation er1 := (scond_raises ORN O1 basesort instance).
Notation eq2 := (eval_squery ORN O2 basesort instance).
Notation eq1 := (eval_squery ORN O1 basesort instance).
Notation es2 := (eval_sspec ORN O2 basesort instance).
Notation es1 := (eval_sspec ORN O1 basesort instance).
Notation ef2 := (eval_sfrom ORN O2 basesort instance).
Notation ef1 := (eval_sfrom ORN O1 basesort instance).

(** the helpers which do not read the interpretations are the same for both dialects *)
Ltac same_helpers :=
  repeat match goal with
         | |- context [?h O2] =>
           lazymatch h with
           | @eval_sexpr _ _ _ => fail | @eval_scond _ _ _ => fail | @scond_raises _ _ _ => fail
           | @eval_squery _ _ _ => fail | @eval_sspec _ _ _ => fail | @eval_sfrom _ _ _ => fail
           | @interp_fun _ => fail | @interp_pred _ => fail | @interp_agg _ => fail | @table_fun _ => fail
           | @eval_window _ => fail | @eval_wsem _ => fail
           | _ => progress change (h O2) with (h O1)
           end
         end.

Ltac rw_ih :=
  repeat match goal with
         | H : forall ce env, ev2 ce env ?x = ev1 ce env ?x |- _ => progress rewrite H
         | H : forall ce env, ec2 ce env ?x = ec1 ce env ?x |- _ => progress rewrite H
         | H : forall ce env, er2 ce env ?x = er1 ce env ?x |- _ => progress rewrite H
         | H : forall ce env, eq2 ce env ?x = eq1 ce env ?x |- _ => progress rewrite H
         | H : forall ce env ex, es2 ce env ?x ex = es1 ce env ?x ex |- _ => progress rewrite H
         | H : forall ce env, ef2 ce env ?x = ef1 ce env ?x |- _ => progress rewrite H
         | H : forall ce env, ef2 ce env ?x = ef1 ce env ?x |- _ => progress rewrite H
         | H : forall y, In y ?l -> forall ce env, ev2 ce env y = ev1 ce env y, Hy : In ?z ?l |- _ =>
           progress rewrite (H z Hy)
         | H : forall y, In y ?l -> forall ce env, ef2 ce env y = ef1 ce env y, Hy : In ?z ?l |- _ =>
           progress rewrite (H z Hy)
         | H : forall e d n, In (O_By e d n) ?l -> forall ce env, ev2 ce env e = ev1 ce env e,
           Hy : In (O_By ?z ?d ?n) ?l |- _ => progress rewrite (H z d n Hy)
         | H : forall e a, In (S_As e a) ?l -> forall ce env, ev2 ce env e = ev1 ce env e,
           Hy : In (S_As ?z ?a) ?l |- _ => progress rewrite (H z a Hy)
         end.

Lemma flat_map_ext_in : forall (X Y : Type) (f g : X -> list Y) l, (forall x, In x l -> f x = g x) -> flat_map f l = flat_map g l.
Proof. intros X Y f g l H; induction l as [ | x l IH]; [reflexivity | ]; simpl; rewrite H, IH; [reflexivity | intros; apply H; right | left]; auto. Qed.

Ltac stop_goal :=
  lazymatch goal with
  | |- fi _ _ = _ => idtac | |- pi _ _ = _ => idtac | |- ai _ _ = _ => idtac | |- tf _ = _ => idtac
  | |- @eval_window _ O2 _ _ _ _ _ _ = _ => idtac
  end.

Ltac cong :=
  same_helpers; rw_ih;
  repeat (first [ reflexivity
                | progress rw_ih
                | match goal with
                  | Ha : forall l, ai ?a l = interp_agg O1 ?a l |- ai ?a _ = interp_agg O1 ?a _ => rewrite Ha
                  | Ha : forall l, pi ?a l = interp_pred O1 ?a l |- pi ?a _ = interp_pred O1 ?a _ => rewrite Ha
                  | Ha : tf ?a = table_fun O1 ?a |- context [tf ?a] => rewrite Ha
                  end
                | stop_goal; fail 1
                | match goal with |- map _ ?l = map _ ?l => apply map_ext_in; intros ? ? end
                | match goal with |- flat_map _ ?l = flat_map _ ?l =>
                                  apply flat_map_ext_in; intros ? ? end
                | match goal with |- ?L = ?R =>
                    lazymatch L with context [match ?a with _ => _ end] =>
                      lazymatch R with context [match ?b with _ => _ end] =>
                        first [ constr_eq a b; destruct a
                              | let E := fresh "E" in assert (E : a = b) by cong; rewrite E; destruct b ] end end end
                | match goal with |- (fun _ => _) = (fun _ => _) => let t := fresh "t" in extensionality t end
                | f_equal ]).

Ltac unf :=
  cbn [eval_sexpr eval_scond scond_raises eval_squery eval_sspec eval_sfrom];
  fold ev1 ev2 ec1 ec2 er1 er2 eq1 eq2 ef1 ef2;
  change (interp_fun O2) with fi; change (interp_pred O2) with pi; change (interp_agg O2) with ai;
  change (table_fun O2) with tf.

Ltac ihc cong_c c := let E := fresh "Ec" in let R := fresh "Rc" in destruct (cong_c c ltac:(assumption)) as [E R].
Ltac ihe cong_e e := let E := fresh "Ee" in assert (E := cong_e e ltac:(assumption)).
Ltac ihq cong_q q := let E := fresh "Eq" in assert (E := cong_q q ltac:(assumption)).

Ltac agr :=
  match goal with
  | Ha : forall l, List.length l = _ -> _ = _ |- _ => apply Ha; rewrite ?map_length; reflexivity
  | Ha : forall l, _ = _ |- _ => apply Ha
  end.

(** the hypotheses of induction for the lists of expressions *)
Ltac ih_l cong_e l :=
  match goal with
  | H : ok (flat_map _ l) |- _ =>
    let IH := fresh "IHl" in
    assert (IH : forall y, In y l -> forall ce env, ev2 ce env y = ev1 ce env y);
    [ clear - cong_e H; revert H; generalize l;
      let go := fresh "go" in fix go 1; intros k Hk y Hy; destruct k as [ | x r]; [destruct Hy | ];
      cbn [flat_map] in Hk; apply ok_app in Hk; destruct Hk as [Hx Hr];
      destruct Hy as [<- | Hy]; [exact (cong_e x Hx) | exact (go r Hr y Hy)]
    | ]
  end.

Ltac ih_o cong_e lo :=
  match goal with
  | H : ok (flat_map _ lo) |- _ =>
    let IH := fresh "IHo" in
    assert (IH : forall e d n, In (O_By e d n) lo -> forall ce env, ev2 ce env e = ev1 ce env e);
    [ clear - cong_e H; revert H; generalize lo;
      let go := fresh "go" in fix go 1; intros k Hk e d n Hy; destruct k as [ | [x d' n'] r]; [destruct Hy | ];
      cbn [flat_map] in Hk; apply ok_app in Hk; destruct Hk as [Hx Hr];
      destruct Hy as [Hy | Hy];
      [let Ex := fresh "Ex" in assert (Ex : x = e) by congruence; rewrite <- Ex; exact (cong_e x Hx) | exact (go r Hr e d n Hy)]
    | ]
  end.

(** ** The parts of the evaluation which the congruence rewrites as a whole *)

Definition ord_rows (O : dialect T) ce env (q : squery T relname) (lo : list (sorder T relname)) :=
  match q with
  | SQ_Select sp => eval_sspec ORN O basesort instance ce env sp (map (fun o => match o with O_By e _ _ => e end) lo)
  | _ => map (fun t => (t, slice_t T relname t :: env)) (eval_squery ORN O basesort instance ce env q)
  end.

Definition ord_keys (O : dialect T) ce (lo : list (sorder T relname)) (x : tuple T * senv T relname) :=
  map (fun o => match o with
                | O_By e _ _ => match is_output_col (fst x) e with
                                | Some v => v
                                | None => eval_sexpr ORN O basesort instance ce (snd x) e
                                end
                end) lo.

Definition flag_rows (O : dialect T) (keys : tuple T * senv T relname -> list value)
           (rows : list (tuple T * senv T relname)) :=
  map (fun x => if existsb (is_error O) (keys x) then (err_row O (fst x), snd x) else x) rows.

Lemma eval_order : forall O ce env q lo off lim,
  eval_squery ORN O basesort instance ce env (SQ_Order q lo off lim) =
  let rows := flag_rows O (ord_keys O ce lo) (ord_rows O ce env q lo) in
  keep_errors O (map (@fst _ _) (offset_limit off lim (sort_on O (map (@sorder_spec T relname) lo) (ord_keys O ce lo) rows)))
              (map (@fst _ _) rows).
Proof. reflexivity. Qed.

Definition fetch_rest (O : dialect T) (lo : list (sorder T relname)) (off : option N) (ties percent : bool) (n : N)
           (keys : tuple T * senv T relname -> list value) (rows : list (tuple T * senv T relname)) :=
  let specs := map (@sorder_spec T relname) lo in
  let sorted := sort_on O specs keys rows in
  let after := match off with Some k => skipn (N.to_nat k) sorted | None => sorted end in
  let count := if percent
               then Nat.div (N.to_nat n * List.length sorted + 99) 100
               else N.to_nat n in
  let first := firstn count after in
  let rest := skipn count after in
  let extra :=
      if ties
      then match rev' first with
           | last :: _ =>
             (fix take (l : list (tuple T * senv T relname)) : list (tuple T * senv T relname) :=
                match l with
                | x :: l' => match compare_keys O specs (keys last) (keys x) with
                             | Eq => x :: take l'
                             | _ => nil
                             end
                | nil => nil
                end) rest
           | nil => nil
           end
      else nil in
  keep_errors O (map (@fst _ _) (first ++ extra)) (map (@fst _ _) rows).

Lemma eval_fetch : forall O ce env q lo off ties pct n,
  eval_squery ORN O basesort instance ce env (SQ_Fetch q lo off ties pct n) =
  fetch_rest O lo off ties pct n (ord_keys O ce lo) (flag_rows O (ord_keys O ce lo) (ord_rows O ce env q lo)).
Proof. reflexivity. Qed.

Definition wcomp (ev : sexpr T relname -> tuple T -> value) :=
  fix comp (f : swfun T relname) : wsem T :=
    match f with
    | W_Agg ag sq e fr => @WS_Agg T ag sq (ev e) fr
    | W_Row_Number _ _ => WS_Row_Number T
    | W_Rank _ _ => WS_Rank T
    | W_Dense_Rank _ _ => WS_Dense_Rank T
    | W_Ntile _ _ n => WS_Ntile T n
    | W_Percent_Rank _ _ => WS_Percent_Rank T
    | W_Cume_Dist _ _ => WS_Cume_Dist T
    | W_Lag e n d => @WS_Shift T true (ev e) n (ev d)
    | W_Lead e n d => @WS_Shift T false (ev e) n (ev d)
    | W_First_Value e fr => @WS_First T (ev e) fr
    | W_Last_Value e fr => @WS_Last T (ev e) fr
    | W_Nth_Value e n fr => @WS_Nth T (ev e) n fr
    | W_Opts f'' ign last => @WS_Opts T (comp f'') ign last
    end.

Definition wfun (O : dialect T) ce env (w : swindow T relname) : list (tuple T) -> list (tuple T) :=
  match w with
  | W_As f lp lo a =>
    let ev e (t : tuple T) := eval_sexpr ORN O basesort instance ce (slice_t T relname t :: env) e in
    let part t := map (fun e => ev e t) lp in
    let keys t := map (fun o => match o with O_By e _ _ => ev e t end) lo in
    fun rows =>
      eval_window O part (map (@sorder_spec T relname) lo) keys a (wcomp ev f)
        (map (fun t => if existsb (is_error O) (part t ++ keys t) then err_row O t else t) rows)
  end.

Lemma eval_windows : forall O ce env q lw,
  eval_squery ORN O basesort instance ce env (SQ_Window q lw) =
  fold_left (fun rows w => w rows) (map (wfun O ce env) lw) (eval_squery ORN O basesort instance ce env q).
Proof. reflexivity. Qed.

(** the aggregates of a window function agree *)
Fixpoint wok (w : wsem T) : Prop :=
  match w with
  | WS_Agg _ ag _ _ _ => forall l, ai ag l = interp_agg O1 ag l
  | WS_Opts w' _ _ => wok w'
  | _ => True
  end.

Fixpoint fagg (f : swfun T relname) : Prop :=
  match f with
  | W_Agg ag _ _ _ => forall l, ai ag l = interp_agg O1 ag l
  | W_Opts f' _ _ => fagg f'
  | _ => True
  end.

Fixpoint swfun_exprs (f : swfun T relname) : list (sexpr T relname) :=
  match f with
  | W_Agg _ _ e _ | W_First_Value e _ | W_Last_Value e _ | W_Nth_Value e _ _ => e :: nil
  | W_Lag e _ d | W_Lead e _ d => e :: d :: nil
  | W_Opts f' _ _ => swfun_exprs f'
  | _ => nil
  end.

Lemma fagg_wok : forall ev f, fagg f -> wok (wcomp ev f).
Proof. intros ev f; induction f; simpl; tauto. Qed.

Lemma wcomp_ext : forall ev ev' f, (forall e, In e (swfun_exprs f) -> ev e = ev' e) -> wcomp ev f = wcomp ev' f.
Proof.
intros ev ev' f; induction f as [ag sq e fr | | | | n | | | e n d | e n d | e fr | e fr | e n fr | f IH ign last];
  intro H; simpl in H |- *; try reflexivity.
- rewrite (H e (or_introl eq_refl)); reflexivity.
- rewrite (H e (or_introl eq_refl)), (H d (or_intror (or_introl eq_refl))); reflexivity.
- rewrite (H e (or_introl eq_refl)), (H d (or_intror (or_introl eq_refl))); reflexivity.
- rewrite (H e (or_introl eq_refl)); reflexivity.
- rewrite (H e (or_introl eq_refl)); reflexivity.
- rewrite (H e (or_introl eq_refl)); reflexivity.
- rewrite (IH H); reflexivity.
Qed.

Lemma eval_wsem_cong : forall w, wok w -> forall a sorted gidx rk i t,
  eval_wsem O2 a w sorted gidx rk i t = eval_wsem O1 a w sorted gidx rk i t.
Proof.
intro w; induction w; intros Hw at0 sorted gidx rk i0 t0; cbn [eval_wsem]; same_helpers; try reflexivity.
- change (interp_agg O2) with ai; simpl in Hw; rewrite Hw; reflexivity.
- simpl in Hw; destruct w; try reflexivity; rewrite IHw by exact Hw; reflexivity.
Qed.

Lemma eval_window_cong : forall part specs keys a w rows, wok w ->
  eval_window O2 part specs keys a w rows = eval_window O1 part specs keys a w rows.
Proof.
intros part specs keys a w rows Hw; unfold eval_window; same_helpers.
apply flat_map_ext; intro g; f_equal; extensionality it; rewrite eval_wsem_cong by exact Hw; reflexivity.
Qed.

Lemma wfun_cong : forall f lp lo a,
  (forall y, In y lp -> forall ce env, ev2 ce env y = ev1 ce env y) ->
  (forall e d n, In (O_By e d n) lo -> forall ce env, ev2 ce env e = ev1 ce env e) ->
  (forall y, In y (swfun_exprs f) -> forall ce env, ev2 ce env y = ev1 ce env y) -> fagg f ->
  forall ce env, wfun O2 ce env (W_As f lp lo a) = wfun O1 ce env (W_As f lp lo a).
Proof.
intros f lp lo a Hp Ho Hf Ha ce env; unfold wfun; extensionality rows.
rewrite eval_window_cong by apply fagg_wok, Ha.
rewrite (wcomp_ext (fun e t => ev2 ce (slice_t T relname t :: env) e) (fun e t => ev1 ce (slice_t T relname t :: env) e))
  by (intros e He; extensionality t; apply Hf; exact He).
cong.
Qed.

Lemma ord_keys_cong : forall lo, (forall e d n, In (O_By e d n) lo -> forall ce env, ev2 ce env e = ev1 ce env e) ->
  forall ce, ord_keys O2 ce lo = ord_keys O1 ce lo.
Proof. intros lo Ho ce; extensionality x; unfold ord_keys; cong. Qed.

Definition gih (g : sgroup T relname) : Prop :=
  match g with
  | G_Fine _ _ => True
  | G_By l | G_Rollup l | G_Cube l => forall y, In y l -> forall ce env, ev2 ce env y = ev1 ce env y
  | G_Sets ss => forall l, In l ss -> forall y, In y l -> forall ce env, ev2 ce env y = ev1 ce env y
  end.

Lemma gkeys_cong : forall g, gih g -> forall ce env,
  gkeys_of ORN O2 basesort instance ce env g = gkeys_of ORN O1 basesort instance ce env g.
Proof.
intros g Hg ce env; extensionality t; unfold gkeys_of; destruct g as [ | l | ss | l | l]; simpl in Hg; try reflexivity.
1, 3, 4: apply map_ext_in; intros y Hy; apply Hg; exact Hy.
induction ss as [ | l ss IH]; [reflexivity | ]; cbn.
rewrite IH by (intros l' Hl'; apply Hg; right; exact Hl').
f_equal; apply map_ext_in; intros y Hy; apply (Hg l (or_introl eq_refl)); exact Hy.
Qed.

Lemma row_vals_cong : forall g, gih g -> forall ce env,
  row_vals_of ORN O2 basesort instance ce env g = row_vals_of ORN O1 basesort instance ce env g.
Proof.
intros g Hg ce env; extensionality t; unfold row_vals_of; destruct g as [ | l | ss | l | l]; simpl in Hg; try reflexivity.
2, 3: apply map_ext_in; intros y Hy; apply Hg; exact Hy.
induction ss as [ | l ss IH]; [reflexivity | ]; cbn.
rewrite IH by (intros l' Hl'; apply Hg; right; exact Hl').
f_equal; apply map_ext_in; intros y Hy; apply (Hg l (or_introl eq_refl)); exact Hy.
Qed.

Lemma where_rows_cong : forall lf w,
  (forall y, In y lf -> forall ce env, ef2 ce env y = ef1 ce env y) ->
  (forall ce env, ec2 ce env w = ec1 ce env w) -> (forall ce env, er2 ce env w = er1 ce env w) ->
  forall ce env, where_rows ORN O2 basesort instance ce env lf w = where_rows ORN O1 basesort instance ce env lf w.
Proof. intros lf w Hf Ec Rc ce env; unfold where_rows; cong. Qed.

Definition sih (s : sselect T relname) : Prop :=
  match s with
  | S_Star _ _ => True
  | S_List l => forall e a, In (S_As e a) l -> forall ce env, ev2 ce env e = ev1 ce env e
  end.

Lemma select_rest_cong : forall s h, sih s ->
  (forall ce env, ec2 ce env h = ec1 ce env h) -> (forall ce env, er2 ce env h = er1 ce env h) ->
  forall ce env sa sq gs,
    select_rest ORN O2 basesort instance ce env sa sq s h gs = select_rest ORN O1 basesort instance ce env sa sq s h gs.
Proof. intros s h Hs Ec Rc ce env sa sq gs; unfold select_rest; destruct s; simpl in Hs; cong. Qed.

Ltac ihf cong_f f := let E := fresh "Ef" in assert (E := cong_f f ltac:(assumption)).

Ltac ih_lf cong_f l :=
  match goal with
  | H : ok (flat_map _ l) |- _ =>
    let IH := fresh "IHf" in
    assert (IH : forall y, In y l -> forall ce env, ef2 ce env y = ef1 ce env y);
    [ clear - cong_f H; revert H; generalize l;
      let go := fresh "go" in fix go 1; intros k Hk y Hy; destruct k as [ | x r]; [destruct Hy | ];
      cbn [flat_map] in Hk; apply ok_app in Hk; destruct Hk as [Hx Hr];
      destruct Hy as [<- | Hy]; [exact (cong_f x Hx) | exact (go r Hr y Hy)]
    | ]
  end.

Ltac ih_s cong_e l :=
  match goal with
  | H : ok (flat_map _ l) |- _ =>
    let IH := fresh "IHs" in
    assert (IH : forall e a, In (S_As e a) l -> forall ce env, ev2 ce env e = ev1 ce env e);
    [ clear - cong_e H; revert H; generalize l;
      let go := fresh "go" in fix go 1; intros k Hk e a Hy; destruct k as [ | [x a'] r]; [destruct Hy | ];
      cbn [flat_map] in Hk; apply ok_app in Hk; destruct Hk as [Hx Hr];
      destruct Hy as [Hy | Hy];
      [let Ex := fresh "Ex" in assert (Ex : x = e) by congruence; rewrite <- Ex; exact (cong_e x Hx)
      | exact (go r Hr e a Hy)]
    | ]
  end.

Fixpoint cong_e (e : sexpr T relname) {struct e} : ok (sexpr_uses e) -> forall ce env, ev2 ce env e = ev1 ce env e
with cong_c (c : scond T relname) {struct c} :
  ok (scond_uses c) -> (forall ce env, ec2 ce env c = ec1 ce env c) /\ (forall ce env, er2 ce env c = er1 ce env c)
with cong_q (q : squery T relname) {struct q} : ok (squery_uses q) -> forall ce env, eq2 ce env q = eq1 ce env q
with cong_s (sp : sspec T relname) {struct sp} : ok (sspec_uses sp) -> forall ce env ex, es2 ce env sp ex = es1 ce env sp ex
with cong_f (f : sfrom T relname) {struct f} : ok (sfrom_uses f) -> forall ce env, ef2 ce env f = ef1 ce env f.
Proof.
- destruct e as [v | a | f l | ag sq e c | ag sq e sep lo c | c e1 e2 | c | q | x]; intros H ce env; split_ok.
  + unf; same_helpers; reflexivity.
  + unf; same_helpers; reflexivity.
  + ih_l cong_e l.
    assert (M : forall ce env, map (ev2 ce env) l = map (ev1 ce env) l)
      by (intros; apply map_ext_in; intros; apply IHl; assumption).
    unf; same_helpers; rewrite M.
    destruct (is_hidden env (E_Fun f l)); [reflexivity | ].
    destruct (first_error O1 _); [reflexivity | ].
    agr.
  + ihc cong_c c; ihe cong_e e.
    unf; same_helpers.
    destruct (is_hidden env _); [reflexivity | ].
    destruct (agg_env _ env) as [ | [[sa g] hid] env']; [agr | ].
    cong. all: try agr.
  + ihc cong_c c; ihe cong_e e. ih_o cong_e lo.
    destruct sep as [s0 | ]; split_ok; [ihe cong_e s0 | ].
    all: unf; same_helpers.
    all: destruct (is_hidden env _); [reflexivity | ].
    all: destruct (agg_env _ env) as [ | [[sa g] hid] env']; [agr | ].
    all: cong. all: try agr.
  + ihc cong_c c; ihe cong_e e1; ihe cong_e e2.
    unf; same_helpers; rw_ih; reflexivity.
  + ihc cong_c c. unf; same_helpers; rw_ih; reflexivity.
  + ihq cong_q q. unf; same_helpers; rw_ih; reflexivity.
  + unf; same_helpers; reflexivity.
- destruct c as [a c1 c2 | c | | p l | e | qtf p l q la | l q la | q]; intros H; split_ok.
  + ihc cong_c c1; ihc cong_c c2; split; intros ce env; unf; cong.
  + ihc cong_c c; split; intros ce env; unf; cong.
  + split; intros ce env; reflexivity.
  + ih_l cong_e l; split; intros ce env; unf; cong.
  + ihe cong_e e; split; intros ce env; unf; cong.
  + ih_l cong_e l; ihq cong_q q; split; intros ce env; unf; cong.
  + ih_l cong_e l; ihq cong_q q; split; intros ce env; unf; cong.
  + ihq cong_q q; split; intros ce env; unf; cong.
- destruct q as [r | o sq q1 q2 | sp | q lo off lim | q lo off ties pct n | q lw | r q1 q2 | sq r q1 q2 q3]; intros H ce env;
  split_ok.
  + reflexivity.
  + ihq cong_q q1; ihq cong_q q2; unf; cong.
  + assert (E := cong_s sp ltac:(assumption)); unf; rw_ih; reflexivity.
  + ih_o cong_e lo.
    assert (R : forall ce env, ord_rows O2 ce env q lo = ord_rows O1 ce env q lo).
    { ihq cong_q q; clear ce env; intros ce env; unfold ord_rows; destruct q; try (rw_ih; reflexivity).
      split_ok; rewrite (cong_s s ltac:(assumption)); reflexivity. }
    rewrite !eval_order, R, (ord_keys_cong lo IHo); same_helpers; reflexivity.
  + ih_o cong_e lo.
    assert (R : forall ce env, ord_rows O2 ce env q lo = ord_rows O1 ce env q lo).
    { ihq cong_q q; clear ce env; intros ce env; unfold ord_rows; destruct q; try (rw_ih; reflexivity).
      split_ok; rewrite (cong_s s ltac:(assumption)); reflexivity. }
    rewrite !eval_fetch, R, (ord_keys_cong lo IHo); same_helpers; reflexivity.
  + ihq cong_q q; rewrite !eval_windows; rw_ih.
    assert (W : forall w, In w lw -> forall ce env, wfun O2 ce env w = wfun O1 ce env w).
    { match goal with Hw : ok (flat_map _ lw) |- _ => clear - cong_e Hw; revert Hw end.
      generalize lw; fix go 1; intros k Hk w Hw; destruct k as [ | w0 r]; [destruct Hw | ].
      cbn [flat_map] in Hk; apply ok_app in Hk; destruct Hk as [H0 Hr].
      destruct Hw as [<- | Hw]; [ | exact (go r Hr w Hw)].
      destruct w0 as [f lp lo a]; split_ok.
      ih_l cong_e lp; ih_o cong_e lo.
      match goal with Hf : ok ?x |- _ => match x with context [f] => rename Hf into HF end end.
      assert (Ha : fagg f) by (clear - HF; revert HF; induction f; cbn; intros; split_ok; auto).
      assert (He : forall y, In y (swfun_exprs f) -> forall ce env, ev2 ce env y = ev1 ce env y).
      { clear - cong_e HF; revert HF; generalize f; fix gof 1; intros f' Hf' y Hy.
        destruct f'; cbn [swfun_exprs] in Hy; cbn in Hf'; split_ok;
          repeat (destruct Hy as [<- | Hy]; [apply cong_e; assumption | ]);
          try contradiction;
          match goal with Hy : In y (swfun_exprs ?g) |- _ => exact (gof g ltac:(assumption) y Hy) end. }
      apply wfun_cong; assumption. }
    f_equal; apply map_ext_in; intros w Hw; apply W; exact Hw.
  + ihq cong_q q1; ihq cong_q q2; unf; cong.
  + ihq cong_q q1; ihq cong_q q2; ihq cong_q q3; unf; rw_ih.
    assert (S : forall r sa, (fun work => eq2 ((r, (sa, work)) :: ce) env q2) = (fun work => eq1 ((r, (sa, work)) :: ce) env q2))
      by (intros; extensionality work; rw_ih; reflexivity).
    rewrite S; same_helpers; reflexivity.
- destruct sp as [sq s lf w g h]; intros H ce env ex; split_ok.
  ihc cong_c w; ihc cong_c h; ih_lf cong_f lf.
  assert (Hs : sih s). { destruct s as [ | l]; [exact I | ]; split_ok; ih_s cong_e l; exact IHs. }
  assert (Hg : gih g).
  { destruct g as [ | l | ss | l | l]; split_ok; try exact I; try (ih_l cong_e l; exact IHl).
    match goal with H : ok ?x |- _ => match x with context [@sexpr_uses T relname] => match x with context [ss] => idtac end end;
      clear - cong_e H; revert H end.
    generalize ss; fix go 1; intros k Hk l Hl y Hy; destruct k as [ | l0 r]; [destruct Hl | ].
    cbn in Hk; apply ok_app in Hk; destruct Hk as [H0 Hr].
    destruct Hl as [<- | Hl]; [ | exact (go r Hr l Hl y Hy)].
    revert H0 y Hy; generalize l0; fix go2 1; intros k' Hk' y Hy; destruct k' as [ | x r']; [destruct Hy | ].
    cbn [flat_map] in Hk'; apply ok_app in Hk'; destruct Hk' as [Hx Hr'].
    destruct Hy as [<- | Hy]; [exact (cong_e x Hx) | exact (go2 r' Hr' y Hy)]. }
  rewrite !eval_select; cbv zeta.
  rewrite (where_rows_cong lf w IHf Ec Rc), (gkeys_cong g Hg), (row_vals_cong g Hg), (select_rest_cong s h Hs Ec0 Rc0).
  same_helpers; reflexivity.
- destruct f as [q rho | jt lat f1 f2 c | name args ord atts]; intros H ce env; split_ok.
  + ihq cong_q q; unf; cong.
  + ihf cong_f f1; ihf cong_f f2; ihc cong_c c; unf; cong.
  + ih_l cong_e args; unf; cong.
Qed.

(** * The congruence

    The evaluation of a query under [O1] and under [O1] with other interpretations ([O2]) is the same when
    the two agree on every function, predicate, aggregate and table function which the query uses. *)
Theorem eval_congruence :
  forall q, ok (squery_uses q) ->
  forall ce env, eval_squery ORN O2 basesort instance ce env q = eval_squery ORN O1 basesort instance ce env q.
Proof. exact cong_q. Qed.

End Sec.
