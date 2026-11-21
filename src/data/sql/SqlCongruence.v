(** * Congruence of the evaluation (TODO 6.2, 6.4)

    The evaluation of a query depends on the dialect only through the interpretations of the functions,
    predicates, aggregates and table functions which the query uses ([squery_uses]), the other fields of the
    record being equal: [eval_congruence]. This is the basis of the refinement between two dialects
    ([Refinement.v]): two dialects which agree on what a query uses give it the same rows. *)
Require Import List Bool String NArith FunctionalExtensionality.
Require Import BasicFacts ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection
        FlatData Bool3 Formula SqlFull SqlInduction.

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
           | @where_rows _ _ _ => fail | @select_rest _ _ _ => fail | @gkeys_of _ _ _ => fail
           | @row_vals_of _ _ _ => fail
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

Lemma fagg_wok : forall ev f, fagg f -> wok (wcomp ev f).
Proof. intros ev f; induction f; simpl; tauto. Qed.

Lemma wcomp_ext : forall ev ev' f, (forall e, In e (wexprs T relname f) -> ev e = ev' e) -> wcomp ev f = wcomp ev' f.
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
  (forall y, In y (wexprs T relname f) -> forall ce env, ev2 ce env y = ev1 ce env y) -> fagg f ->
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

(** the hypotheses of induction, once the constructs of the sub-terms are known to agree *)
Ltac prep :=
  intros; split_ok;
  repeat match goal with
         | H : ok ?u -> _, K : ok ?u |- _ => specialize (H K)
         | H : (forall ce env, _) /\ (forall ce env, _) |- _ => destruct H
         | H : forall y, In y ?l -> ok _ -> _, K : ok (flat_map _ ?l) |- _ =>
           let H' := fresh "IHl" in pose proof (fun y Hy => H y Hy (ok_flat_map _ _ _ K y Hy)) as H'; clear H
         | H : forall e d n, In (O_By e d n) ?l -> ok _ -> _, K : ok (flat_map _ ?l) |- _ =>
           let H' := fresh "IHo" in pose proof (fun e d n Hy => H e d n Hy (ok_flat_map _ _ _ K _ Hy)) as H'; clear H
         | H : forall e a, In (S_As e a) ?l -> ok _ -> _, K : ok (flat_map _ ?l) |- _ =>
           let H' := fresh "IHs" in pose proof (fun e a Hy => H e a Hy (ok_flat_map _ _ _ K _ Hy)) as H'; clear H
         end.

Definition Pe_ (e : sexpr T relname) := ok (sexpr_uses e) -> forall ce env, ev2 ce env e = ev1 ce env e.
Definition Pc_ (c : scond T relname) :=
  ok (scond_uses c) -> (forall ce env, ec2 ce env c = ec1 ce env c) /\ (forall ce env, er2 ce env c = er1 ce env c).
Definition Pq_ (q : squery T relname) := ok (squery_uses q) -> forall ce env, eq2 ce env q = eq1 ce env q.
Definition Ps_ (sp : sspec T relname) := ok (sspec_uses sp) -> forall ce env ex, es2 ce env sp ex = es1 ce env sp ex.
Definition Pf_ (f : sfrom T relname) := ok (sfrom_uses f) -> forall ce env, ef2 ce env f = ef1 ce env f.

Ltac open_case := unfold Pe_, Pc_, Pq_, Ps_, Pf_, LE, LO; cbv beta.

Lemma c_const : forall v, Pe_ (E_Const T relname v).
Proof.
open_case.
prep; unf; same_helpers; reflexivity.
Qed.

Lemma c_col : forall a, Pe_ (E_Col T relname a).
Proof.
open_case.
prep; unf; same_helpers; reflexivity.
Qed.

Lemma c_fun : forall f l, LE T relname Pe_ l -> Pe_ (E_Fun f l).
Proof.
open_case.
prep.
assert (M : forall ce env, map (ev2 ce env) l = map (ev1 ce env) l)
  by (intros; apply map_ext_in; intros; apply IHl; assumption).
unf; same_helpers; rewrite M.
destruct (is_hidden env (E_Fun f l)); [reflexivity | ].
destruct (first_error O1 _); [reflexivity | ].
agr.
Qed.

Lemma c_agg : forall ag sq e c, Pe_ e -> Pc_ c -> Pe_ (E_Agg ag sq e c).
Proof.
open_case.
prep; unf; same_helpers; destruct (is_hidden env _); [reflexivity | ].
destruct (agg_env _ env) as [ | [[sa g] hid] env']; [agr | cong; try agr].
Qed.

Lemma c_aggx : forall ag sq e sep lo c, Pe_ e -> (forall s, sep = Some s -> Pe_ s) -> LO T relname Pe_ lo -> Pc_ c -> Pe_ (E_AggX ag sq e sep lo c).
Proof.
open_case.
intros ag sq e sep lo c He Hs Ho Hc H ce env.
destruct sep as [s0 | ]; [specialize (Hs s0 eq_refl) | clear Hs]; prep.
all: unf; same_helpers; destruct (is_hidden env _); [reflexivity | ].
all: destruct (agg_env _ env) as [ | [[sa g] hid] env']; [agr | cong; try agr].
Qed.

Lemma c_case : forall c e1 e2, Pc_ c -> Pe_ e1 -> Pe_ e2 -> Pe_ (E_Case c e1 e2).
Proof.
open_case.
prep; unf; same_helpers; rw_ih; reflexivity.
Qed.

Lemma c_cond : forall c, Pc_ c -> Pe_ (E_Cond c).
Proof.
open_case.
prep; unf; same_helpers; rw_ih; reflexivity.
Qed.

Lemma c_sub : forall q, Pq_ q -> Pe_ (E_Sub q).
Proof.
open_case.
prep; unf; same_helpers; rw_ih; reflexivity.
Qed.

Lemma c_grouping : forall x, Pe_ x -> Pe_ (E_Grouping x).
Proof.
open_case.
prep; unf; same_helpers; reflexivity.
Qed.

Lemma c_conj : forall a c1 c2, Pc_ c1 -> Pc_ c2 -> Pc_ (C_Conj a c1 c2).
Proof.
open_case.
prep; split; intros; unf; cong.
Qed.

Lemma c_not : forall c, Pc_ c -> Pc_ (C_Not c).
Proof.
open_case.
prep; split; intros; unf; cong.
Qed.

Lemma c_true : Pc_ (C_True T relname).
Proof.
open_case.
split; intros; reflexivity.
Qed.

Lemma c_pred : forall p l, LE T relname Pe_ l -> Pc_ (C_Pred p l).
Proof.
open_case.
prep; split; intros; unf; cong.
Qed.

Lemma c_expr : forall e, Pe_ e -> Pc_ (C_Expr e).
Proof.
open_case.
prep; split; intros; unf; cong.
Qed.

Lemma c_quant : forall qtf p l q la, LE T relname Pe_ l -> Pq_ q -> Pc_ (C_Quant qtf p l q la).
Proof.
open_case.
prep; split; intros; unf; cong.
Qed.

Lemma c_in : forall l q la, LE T relname Pe_ l -> Pq_ q -> Pc_ (C_In l q la).
Proof.
open_case.
prep; split; intros; unf; cong.
Qed.

Lemma c_exists : forall q, Pq_ q -> Pc_ (C_Exists q).
Proof.
open_case.
prep; split; intros; unf; cong.
Qed.

Lemma c_table : forall r, Pq_ (SQ_Table T r).
Proof.
open_case.
intros; reflexivity.
Qed.

Lemma c_set : forall o sq q1 q2, Pq_ q1 -> Pq_ q2 -> Pq_ (SQ_Set o sq q1 q2).
Proof.
open_case.
prep; unf; cong.
Qed.

Lemma c_select : forall sp, Ps_ sp -> Pq_ (SQ_Select sp).
Proof.
open_case.
prep; unf; rw_ih; reflexivity.
Qed.

Lemma c_order : forall q lo off lim, Pq_ q -> (forall sp, q = SQ_Select sp -> Ps_ sp) -> LO T relname Pe_ lo -> Pq_ (SQ_Order q lo off lim).
Proof.
open_case.
intros q lo off lim Hq Hsp Ho H ce env; prep.
assert (R : forall ce env, ord_rows O2 ce env q lo = ord_rows O1 ce env q lo).
{ clear ce env; intros ce env; unfold ord_rows; destruct q; try (rw_ih; reflexivity).
  split_ok; rewrite (Hsp s eq_refl ltac:(assumption)); reflexivity. }
rewrite !eval_order, R, (ord_keys_cong lo IHo); same_helpers; reflexivity.
Qed.

Lemma c_fetch : forall q lo off ties pct n, Pq_ q -> (forall sp, q = SQ_Select sp -> Ps_ sp) -> LO T relname Pe_ lo -> Pq_ (SQ_Fetch q lo off ties pct n).
Proof.
open_case.
intros q lo off ties pct n Hq Hsp Ho H ce env; prep.
assert (R : forall ce env, ord_rows O2 ce env q lo = ord_rows O1 ce env q lo).
{ clear ce env; intros ce env; unfold ord_rows; destruct q; try (rw_ih; reflexivity).
  split_ok; rewrite (Hsp s eq_refl ltac:(assumption)); reflexivity. }
rewrite !eval_fetch, R, (ord_keys_cong lo IHo); same_helpers; reflexivity.
Qed.

Lemma c_window : forall q lw, Pq_ q -> (forall f lp lo a, In (W_As f lp lo a) lw -> LE T relname Pe_ lp /\ LO T relname Pe_ lo /\ LE T relname Pe_ (wexprs T relname f)) -> Pq_ (SQ_Window q lw).
Proof.
open_case.
intros q lw Hq Hw H ce env; prep; rewrite !eval_windows; rw_ih.
assert (W : forall w, In w lw -> forall ce env, wfun O2 ce env w = wfun O1 ce env w).
{ intros [f lp lo a] Iw.
  match goal with K : ok (flat_map _ lw) |- _ => assert (K' := ok_flat_map _ _ _ K _ Iw) end.
  destruct (Hw f lp lo a Iw) as [Hp [Ho Hf]]; clear Hw; cbv beta in K'; split_ok.
  assert (IHp : forall y, In y lp -> forall ce env, ev2 ce env y = ev1 ce env y)
    by (intros y Hy; apply Hp; [exact Hy | ]; match goal with K : ok (flat_map _ lp) |- _ => exact (ok_flat_map _ _ _ K y Hy) end).
  match goal with K : ok (flat_map ?U lo), K2 : ok (flat_map ?V lo) |- _ =>
    assert (IHo : forall e d n, In (O_By e d n) lo -> forall ce env, ev2 ce env e = ev1 ce env e)
      by (intros e d n Hy; apply (Ho e d n Hy); first [exact (ok_flat_map _ _ _ K _ Hy) | exact (ok_flat_map _ _ _ K2 _ Hy)])
  end.
  match goal with HF : ok ?x |- _ => match x with context [f] => rename HF into HFf end end.
  assert (Ha : fagg f) by (clear - HFf; revert HFf; induction f; cbn; intros; split_ok; auto).
  assert (He : forall y, In y (wexprs T relname f) -> forall ce env, ev2 ce env y = ev1 ce env y).
  { intros y Hy; apply Hf; [exact Hy | ]; clear - HFf Hy; revert HFf y Hy; induction f; intros HFf y Hy;
      cbn in HFf, Hy; split_ok; try contradiction;
      repeat (destruct Hy as [<- | Hy]; [assumption | ]); try contradiction; auto. }
  apply wfun_cong; assumption. }
f_equal; apply map_ext_in; intros w Hw'; apply W; exact Hw'.
Qed.

Lemma c_with : forall r q1 q2, Pq_ q1 -> Pq_ q2 -> Pq_ (SQ_With r q1 q2).
Proof.
open_case.
prep; unf; cong.
Qed.

Lemma c_withrec : forall sq r q1 q2 q3, Pq_ q1 -> Pq_ q2 -> Pq_ q3 -> Pq_ (SQ_WithRec sq r q1 q2 q3).
Proof.
open_case.
prep; unf; rw_ih.
assert (S : forall r sa, (fun work => eq2 ((r, (sa, work)) :: ce) env q2) = (fun work => eq1 ((r, (sa, work)) :: ce) env q2))
  by (intros; extensionality work; rw_ih; reflexivity).
rewrite S; same_helpers; reflexivity.
Qed.

Lemma c_spec : forall sq s lf w g h,
  match s with S_Star _ _ => True | S_List l => forall e a, In (S_As e a) l -> Pe_ e end ->
  (forall f, In f lf -> Pf_ f) -> Pc_ w ->
  match g with
  | G_Fine _ _ => True
  | G_By l | G_Rollup l | G_Cube l => LE T relname Pe_ l
  | G_Sets ss => forall l, In l ss -> LE T relname Pe_ l
  end -> Pc_ h -> Ps_ (Select sq s lf w g h).
Proof.
open_case.
intros sq s lf w g h Hs Hf Hw Hg Hh H ce env ex; split_ok.
specialize (Hw ltac:(assumption)); specialize (Hh ltac:(assumption)); destruct Hw as [Ec Rc]; destruct Hh as [Ec0 Rc0].
assert (IHf : forall y, In y lf -> forall ce env, ef2 ce env y = ef1 ce env y)
  by (intros y Hy; apply Hf; [exact Hy | ]; match goal with K : ok (flat_map _ lf) |- _ => exact (ok_flat_map _ _ _ K y Hy) end).
assert (Hs' : sih s).
{ destruct s as [ | l]; [exact I | ]; split_ok; intros e a Hy; apply (Hs e a Hy).
  match goal with K : ok (flat_map _ l) |- _ => exact (ok_flat_map _ _ _ K _ Hy) end. }
assert (Hg' : gih g).
{ destruct g as [ | l | ss | l | l]; split_ok; try exact I.
  1, 3, 4: intros y Hy; apply (Hg y Hy); match goal with K : ok (flat_map _ ?L), Hy : In y ?L |- _ => exact (ok_flat_map _ _ _ K y Hy) end.
  match goal with K : ok ?x |- _ => match x with context [@sexpr_uses T relname] => match x with context [ss] => idtac end end;
    rename K into KS end.
  intros l Hl y Hy; apply (Hg l Hl y Hy); clear - KS Hl Hy.
  induction ss as [ | l0 ss IH]; [destruct Hl | ]; cbn in KS; apply ok_app in KS; destruct KS as [K1 K2].
  destruct Hl as [<- | Hl]; [exact (ok_flat_map _ _ _ K1 y Hy) | exact (IH K2 Hl)]. }
rewrite !eval_select; cbv zeta.
rewrite (where_rows_cong lf w IHf Ec Rc), (gkeys_cong g Hg'), (row_vals_cong g Hg'), (select_rest_cong s h Hs' Ec0 Rc0).
same_helpers; reflexivity.
Qed.

Lemma c_fquery : forall q rho, Pq_ q -> Pf_ (Fr_Query q rho).
Proof.
open_case.
prep; unf; cong.
Qed.

Lemma c_fjoin : forall jt lat f1 f2 c, Pf_ f1 -> Pf_ f2 -> Pc_ c -> Pf_ (Fr_Join jt lat f1 f2 c).
Proof.
open_case.
prep; unf; cong.
Qed.

Lemma c_ffun : forall name args ord atts, LE T relname Pe_ args -> Pf_ (Fr_Fun name args ord atts).
Proof.
open_case.
prep; unf; cong.
Qed.

Lemma cong_all : forall q, ok (squery_uses q) -> forall ce env, eq2 ce env q = eq1 ce env q.
Proof.
exact (ind_q T relname Pe_ Pc_ Pq_ Ps_ Pf_ c_const c_col c_fun c_agg c_aggx c_case c_cond c_sub c_grouping
         c_conj c_not c_true c_pred c_expr c_quant c_in c_exists c_table c_set c_select c_order c_fetch c_window
         c_with c_withrec c_spec c_fquery c_fjoin c_ffun).
Qed.

(** * The congruence

    The evaluation of a query under [O1] and under [O1] with other interpretations ([O2]) is the same when
    the two agree on every function, predicate, aggregate and table function which the query uses. *)
Theorem eval_congruence :
  forall q, ok (squery_uses q) ->
  forall ce env, eval_squery ORN O2 basesort instance ce env q = eval_squery ORN O1 basesort instance ce env q.
Proof. exact cong_all. Qed.

End Sec.
