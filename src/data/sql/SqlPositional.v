(** * A positional semantics and its named view (TODO 6.3, issue I4)

    In SQL a row is a list of values and the names of the columns are metadata, which may repeat:
    [SELECT * FROM t, t] has the columns of [t] twice, and [SELECT * FROM (SELECT a AS x, b AS x FROM t)] is
    a derived table with two columns [x]. The tuples of [SqlFull.v] are named, so that such queries cannot be
    written directly. This file gives a positional semantics ([peval]: rows as lists of values, names as
    metadata, [pnames]) to a language of tables, selections, [SELECT *] over products and [UNION ALL], and
    compiles it to [SqlFull.v] ([pq_to]): the columns of a query are put at the attributes [pa 0], [pa 1], ...,
    and the columns of the [i]-th item of a [FROM] clause are renamed to follow those of the items before it,
    so that the named product has every column of every item. [positional_agree]: the rows of the compiled
    query, read by position, are the rows of the positional semantics, in the same order. The named
    semantics and its lemmas are unchanged: it is the named view of the positional one.

    The dialect has no error value ([Herr], [Hpe]), converts nothing before a comparison ([Hcoerce]), its NULLs
    have no type ([Hnull]), and it does not convert the columns of a set operation ([Hun]); the positional
    attributes are distinct ([Hpa]), and the stored rows have the attributes of their table ([Hinst]). *)
Require Import List Bool Arith Lia.
Require Import BasicFacts ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection FlatData Bool3 Formula SqlFull SqlRelate SqlRelateSelect.
Import Tuple.

Section Sec.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.
Hypothesis ORN : Oset.Rcd relname.
Hypothesis O : dialect T.
Hypothesis basesort : relname -> Fset.set (A T).
Hypothesis instance : relname -> Febag.bag (Fecol.CBag (CTuple T)).

Notation sexpr := (SqlFull.sexpr T relname).
Notation scond := (SqlFull.scond T relname).
Notation squery := (SqlFull.squery T relname).
Notation ev := (eval_sexpr ORN O basesort instance nil).
Notation ec := (eval_scond ORN O basesort instance nil).
Notation er := (scond_raises ORN O basesort instance nil).
Notation eq0 := (eval_squery ORN O basesort instance nil nil).
Notation ef0 := (eval_sfrom ORN O basesort instance nil nil).

(** the positional attributes *)
Hypothesis pa : nat -> attribute T.

(** * Syntax *)

Inductive pexpr : Type :=
  | PE_Col : nat -> pexpr
  | PE_Const : value T -> pexpr
  | PE_Fun : symbol T -> list pexpr -> pexpr.

Inductive pcond : Type :=
  | PC_True : pcond
  | PC_Pred : predicate T -> list pexpr -> pcond
  | PC_Conj : and_or -> pcond -> pcond -> pcond
  | PC_Not : pcond -> pcond.

Inductive pquery : Type :=
  | PQ_Table : relname -> pquery
  | PQ_Select : list (attribute T * pexpr) -> list pquery -> pcond -> pquery
  | PQ_Star : list pquery -> pcond -> pquery
  | PQ_Union : pquery -> pquery -> pquery.

(** the names of the columns, which may repeat, and their number *)
Fixpoint pnames (q : pquery) : list (attribute T) :=
  match q with
  | PQ_Table r => {{{basesort r}}}
  | PQ_Select items _ _ => map (@fst _ _) items
  | PQ_Star lf _ => flat_map pnames lf
  | PQ_Union q1 _ => pnames q1
  end.

Fixpoint parity (q : pquery) : nat :=
  match q with
  | PQ_Table r => length ({{{basesort r}}})
  | PQ_Select items _ _ => length items
  | PQ_Star lf _ => fold_right (fun q n => parity q + n) 0 lf
  | PQ_Union q1 _ => parity q1
  end.

Lemma length_pnames : forall q, length (pnames q) = parity q.
Proof.
fix IH 1; intros [r | items lf w | lf w | q1 q2]; cbn [pnames parity]; [reflexivity | apply map_length | | apply IH].
induction lf as [ | q lf IHl]; [reflexivity | cbn [flat_map fold_right]; rewrite app_length, IH, IHl; reflexivity].
Qed.

(** * The positional semantics *)

Fixpoint pe_eval (row : list (value T)) (e : pexpr) : value T :=
  match e with
  | PE_Col i => nth i row (null_of T (pa i))
  | PE_Const v => const_of O v
  | PE_Fun f l => interp_fun O f (map (pe_eval row) l)
  end.

Fixpoint pc_eval (row : list (value T)) (c : pcond) : Bool.b (B T) :=
  match c with
  | PC_True => Bool.true (B T)
  | PC_Pred p l => interp_pred O p (map (pe_eval row) l)
  | PC_Conj a c1 c2 => interp_conj (B T) a (pc_eval row c1) (pc_eval row c2)
  | PC_Not c => Bool.negb (B T) (pc_eval row c)
  end.

(** the product of lists of rows: the combinations, the left item first *)
Definition pprod (Ls : list (list (list (value T)))) : list (list (value T)) :=
  fold_left (fun acc l => flat_map (fun x => map (fun y => x ++ y) l) acc) Ls (nil :: nil).

Fixpoint peval (q : pquery) : list (list (value T)) :=
  match q with
  | PQ_Table r => map (fun t => map (dot T t) ({{{basesort r}}})) (Febag.elements _ (instance r))
  | PQ_Select items lf w =>
    map (fun row => map (fun p => pe_eval row (snd p)) items)
        (filter (fun row => is_true3 T (pc_eval row w)) (pprod (map peval lf)))
  | PQ_Star lf w => filter (fun row => is_true3 T (pc_eval row w)) (pprod (map peval lf))
  | PQ_Union q1 q2 => if Nat.eqb (parity q1) (parity q2) then peval q1 ++ peval q2 else nil
  end.

(** * The compilation to the named semantics *)

Fixpoint pe_to (e : pexpr) : sexpr :=
  match e with
  | PE_Col i => E_Col T relname (pa i)
  | PE_Const v => E_Const T relname v
  | PE_Fun f l => E_Fun f (map pe_to l)
  end.

Fixpoint pc_to (c : pcond) : scond :=
  match c with
  | PC_True => C_True T relname
  | PC_Pred p l => C_Pred p (map pe_to l)
  | PC_Conj a c1 c2 => C_Conj a (pc_to c1) (pc_to c2)
  | PC_Not c => C_Not (pc_to c)
  end.

(** the items [e0 AS pa k], [e1 AS pa (k + 1)], ... *)
Fixpoint sitems (k : nat) (es : list sexpr) : list (sitem T relname) :=
  match es with
  | nil => nil
  | e :: es => S_As e (pa k) :: sitems (S k) es
  end.

(** the renaming of [pa i], ..., [pa (i + n - 1)] to [pa (off + i)], ... *)
Fixpoint shiftp (i off n : nat) : list (attribute T * attribute T) :=
  match n with
  | 0 => nil
  | S n => (pa i, pa (off + i)) :: shiftp (S i) off n
  end.

Definition psel (es : list sexpr) (lf : list (sfrom T relname)) (c : scond) : squery :=
  SQ_Select (Select Set_All (S_List (sitems 0 es)) lf c (G_Fine T relname) (C_True T relname)).

Fixpoint pq_to (q : pquery) : squery :=
  match q with
  | PQ_Table r =>
    psel (map (E_Col T relname) ({{{basesort r}}})) (Fr_Query (SQ_Table T r) (Ren_Star T) :: nil) (C_True T relname)
  | PQ_Select items lf w =>
    psel (map (fun p => pe_to (snd p)) items)
         ((fix go (off : nat) (lf : list pquery) : list (sfrom T relname) :=
             match lf with
             | nil => nil
             | q :: lf => Fr_Query (pq_to q) (Ren_List T (shiftp 0 off (parity q))) :: go (off + parity q) lf
             end) 0 lf) (pc_to w)
  | PQ_Star lf w =>
    SQ_Select (Select Set_All (S_Star T relname)
         ((fix go (off : nat) (lf : list pquery) : list (sfrom T relname) :=
             match lf with
             | nil => nil
             | q :: lf => Fr_Query (pq_to q) (Ren_List T (shiftp 0 off (parity q))) :: go (off + parity q) lf
             end) 0 lf) (pc_to w) (G_Fine T relname) (C_True T relname))
  | PQ_Union q1 q2 => SQ_Set Union Set_All (pq_to q1) (pq_to q2)
  end.

Fixpoint pfrom (off : nat) (lf : list pquery) : list (sfrom T relname) :=
  match lf with
  | nil => nil
  | q :: lf => Fr_Query (pq_to q) (Ren_List T (shiftp 0 off (parity q))) :: pfrom (off + parity q) lf
  end.

Lemma pq_to_unfold : forall q, pq_to q =
  match q with
  | PQ_Table r =>
    psel (map (E_Col T relname) ({{{basesort r}}})) (Fr_Query (SQ_Table T r) (Ren_Star T) :: nil) (C_True T relname)
  | PQ_Select items lf w => psel (map (fun p => pe_to (snd p)) items) (pfrom 0 lf) (pc_to w)
  | PQ_Star lf w => SQ_Select (Select Set_All (S_Star T relname) (pfrom 0 lf) (pc_to w) (G_Fine T relname) (C_True T relname))
  | PQ_Union q1 q2 => SQ_Set Union Set_All (pq_to q1) (pq_to q2)
  end.
Proof. intros [r | items lf w | lf w | q1 q2]; reflexivity. Qed.


(** * The positions *)

Hypothesis Hpa : forall i j, pa i = pa j -> i = j.

Definition rangeS (k n : nat) := Fset.mk_set (A T) (map pa (seq k n)).

Lemma mem_range : forall i k n, Fset.mem (A T) (pa i) (rangeS k n) = (k <=? i) && (i <? k + n).
Proof.
intros i k n; unfold rangeS; rewrite Fset.mem_mk_set.
destruct (Oset.mem_bool (OAtt T) (pa i) (map pa (seq k n))) eqn:M; symmetry.
- rewrite Oset.mem_bool_true_iff, in_map_iff in M; destruct M as [j [Ej Ij]]; apply Hpa in Ej; subst j.
  rewrite in_seq in Ij; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia.
- apply not_true_iff_false; intro K; apply andb_true_iff in K; destruct K as [K1 K2].
  apply Nat.leb_le in K1; apply Nat.ltb_lt in K2.
  rewrite <- not_true_iff_false in M; apply M; rewrite Oset.mem_bool_true_iff, in_map_iff.
  exists i; split; [reflexivity | rewrite in_seq; lia].
Qed.

Lemma range_union : forall k a b, (rangeS k a unionS rangeS (k + a) b) =S= rangeS k (a + b).
Proof.
intros k a b; unfold rangeS; rewrite Fset.equal_spec; intro x.
rewrite Fset.mem_union, !Fset.mem_mk_set, seq_app, map_app, Oset.mem_bool_app; reflexivity.
Qed.

Lemma range_equal : forall n1 n2, Fset.equal (A T) (rangeS 0 n1) (rangeS 0 n2) = Nat.eqb n1 n2.
Proof.
intros n1 n2; destruct (Nat.eqb n1 n2) eqn:E; [apply Nat.eqb_eq in E; subst; apply Fset.equal_refl | ].
apply not_true_iff_false; intro K; rewrite Fset.equal_spec in K; apply Nat.eqb_neq in E.
destruct (Nat.lt_ge_cases n1 n2) as [L | L].
- generalize (K (pa n1)); rewrite !mem_range; simpl.
  replace (n1 <? n1) with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (n1 <? n2) with true by (symmetry; apply Nat.ltb_lt; lia); discriminate.
- generalize (K (pa n2)); rewrite !mem_range; simpl.
  replace (n2 <? n2) with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (n2 <? n1) with true by (symmetry; apply Nat.ltb_lt; lia); discriminate.
Qed.

(** the values of a tuple at the positions [k], ..., [k + n - 1] *)
Definition readat (k n : nat) (t : tuple T) : list (value T) := map (fun j => dot T t (pa (k + j))) (seq 0 n).

Lemma map_seq_shift : forall (X : Type) (f : nat -> X) k n, map f (seq k n) = map (fun j => f (k + j)) (seq 0 n).
Proof.
intros X f k n; revert f k; induction n as [ | n IH]; intros f k; [reflexivity | ].
cbn [seq map]; rewrite Nat.add_0_r; f_equal.
rewrite (IH f (S k)), (IH (fun j => f (k + j)) 1); apply map_ext; intro j; f_equal; lia.
Qed.

Lemma nth_map_seq : forall (X : Type) (f : nat -> X) k n i d,
  nth i (map f (seq k n)) d = if i <? n then f (k + i) else d.
Proof.
intros X f k n; revert k; induction n as [ | n IH]; intros k i d; [destruct i; reflexivity | ].
destruct i as [ | i]; cbn [seq map nth]; [rewrite Nat.add_0_r; reflexivity | ].
rewrite IH; replace (S i <? S n) with (i <? n) by reflexivity; destruct (i <? n); [f_equal; lia | reflexivity].
Qed.

Lemma map_nth_all : forall (X : Type) (l : list X) d, map (fun j => nth j l d) (seq 0 (length l)) = l.
Proof.
intros X l d; induction l as [ | x l IH]; [reflexivity | ].
cbn [length seq map nth]; f_equal; rewrite map_seq_shift; exact IH.
Qed.

Fixpoint pairs (k : nat) (vs : list (value T)) : list (attribute T * value T) :=
  match vs with
  | nil => nil
  | v :: vs => (pa k, v) :: pairs (S k) vs
  end.

Lemma fst_pairs : forall vs k, map (@fst _ _) (pairs k vs) = map pa (seq k (length vs)).
Proof. intro vs; induction vs as [ | v vs IH]; intro k; [reflexivity | simpl; f_equal; apply IH]. Qed.

Lemma find_cons : forall (X : Type) a a' (b : X) l,
  Oset.find (OAtt T) a ((a', b) :: l) = if Oset.eq_bool (OAtt T) a a' then Some b else Oset.find (OAtt T) a l.
Proof. reflexivity. Qed.

Lemma find_pairs : forall vs k j d, j < length vs ->
  Oset.find (OAtt T) (pa (k + j)) (pairs k vs) = Some (nth j vs d).
Proof.
intro vs; induction vs as [ | v vs IH]; intros k j d L; [simpl in L; lia | ].
cbn [pairs]; rewrite find_cons; destruct j as [ | j].
- rewrite Nat.add_0_r, Oset.eq_bool_refl; reflexivity.
- destruct (Oset.eq_bool (OAtt T) (pa (k + S j)) (pa k)) eqn:E.
  + rewrite Oset.eq_bool_true_iff in E; apply Hpa in E; lia.
  + replace (k + S j) with (S k + j) by lia; apply IH; simpl in L; lia.
Qed.

Hypothesis Herr : forall v, is_error O v = false.
Hypothesis Hpe : forall p l, pred_error O p l = false.
Hypothesis Hcoerce : forall p ks l, cmp_coerce O p ks l = l.
Hypothesis Hnull : forall a v, is_null O v = true -> null_of T a = v.
Hypothesis Hun : forall l, unify_column O l = l.
Hypothesis Hinst : forall r t, In t (Febag.elements _ (instance r)) -> labels T t =S= basesort r.

Lemma store_id : forall a v, store O a v = v.
Proof. intros a v; unfold store; destruct (is_null O v) eqn:N; [apply Hnull; exact N | reflexivity]. Qed.

Lemma labels_mk_row_pairs : forall vs, labels T (mk_row O (pairs 0 vs)) =S= rangeS 0 (length vs).
Proof. intro vs; unfold mk_row; rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)), fst_pairs; apply Fset.equal_refl. Qed.

Lemma read_mk_row : forall vs, readat 0 (length vs) (mk_row O (pairs 0 vs)) = vs.
Proof.
intro vs; unfold readat; rewrite <- (map_nth_all _ vs (null_of T (pa 0))) at 2.
apply map_ext_in; intros j Ij; rewrite in_seq in Ij.
unfold mk_row; rewrite dot_mk_tuple, fst_pairs.
replace (Fset.mem (A T) (pa (0 + j)) (Fset.mk_set (A T) (map pa (seq 0 (length vs))))) with true
  by (symmetry; fold (rangeS 0 (length vs)); rewrite mem_range; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
rewrite (find_pairs vs 0 j (null_of T (pa 0))) by lia; apply store_id.
Qed.


(** * Expressions and conditions *)

Lemma pe_agree : forall N t, labels T t =S= rangeS 0 N ->
  forall e, ev (slice_t T relname t :: nil) (pe_to e) = pe_eval (readat 0 N t) e.
Proof.
intros N t Ht; fix IH 1; intros [i | v | f l].
- cbn [pe_to pe_eval eval_sexpr]; unfold is_hidden; cbn [lookup slice_t]; unfold readat; rewrite nth_map_seq.
  rewrite (Fset.mem_eq_2 _ _ _ Ht), mem_range; cbn [Nat.leb andb Nat.add]; destruct (i <? N); reflexivity.
- reflexivity.
- cbn [pe_to pe_eval]; change (ev (slice_t T relname t :: nil) (E_Fun f (map pe_to l))) with
    (if is_hidden (slice_t T relname t :: nil) (E_Fun f (map pe_to l)) then null O
     else let vs := map (ev (slice_t T relname t :: nil)) (map pe_to l) in
          match first_error O (if lazy_symbol O f then firstn 1 vs else vs) with
          | Some err => err | None => interp_fun O f vs end).
  replace (is_hidden (slice_t T relname t :: nil) (E_Fun f (map pe_to l))) with false by reflexivity.
  cbv zeta; rewrite (first_error_none T O Herr), map_map; f_equal.
  induction l as [ | x l IHl]; [reflexivity | simpl; rewrite IH, IHl; reflexivity].
Qed.

Lemma vals_ok : forall l : list (value T), existsb (is_error O) l = false.
Proof. intro l; induction l as [ | v l IH]; [reflexivity | simpl; rewrite Herr; exact IH]. Qed.

Lemma pc_agree : forall N t, labels T t =S= rangeS 0 N ->
  forall c, ec (slice_t T relname t :: nil) (pc_to c) = pc_eval (readat 0 N t) c /\
            er (slice_t T relname t :: nil) (pc_to c) = false.
Proof.
intros N t Ht c; induction c as [ | p l | a c1 IH1 c2 IH2 | c IH].
- split; reflexivity.
- cbn [pc_to pc_eval eval_scond scond_raises]; fold ev; rewrite Hcoerce, Hpe, vals_ok; split; [ | reflexivity].
  f_equal; rewrite map_map; apply map_ext; intro e; apply (pe_agree N t Ht).
- destruct IH1 as [E1 R1]; destruct IH2 as [E2 R2].
  cbn [pc_to pc_eval eval_scond scond_raises]; fold ec er; rewrite E1, E2, R1, R2; split; reflexivity.
- destruct IH as [E1 R1]; cbn [pc_to pc_eval eval_scond scond_raises]; fold ec er; rewrite E1, R1; split; reflexivity.
Qed.

Lemma pc_noraise : forall t c, er (slice_t T relname t :: nil) (pc_to c) = false.
Proof.
intros t c; induction c as [ | p l | a c1 IH1 c2 IH2 | c IH]; [reflexivity | | | ].
- cbn [pc_to scond_raises]; rewrite Hpe, vals_ok; reflexivity.
- cbn [pc_to scond_raises]; fold er; rewrite IH1, IH2; reflexivity.
- cbn [pc_to scond_raises]; fold er; exact IH.
Qed.

Lemma pe_no_agg : forall sa e, sexpr_has_agg ORN basesort nil sa (pe_to e) = false.
Proof.
intro sa; fix IH 1; intros [i | v | f l]; [reflexivity | reflexivity | ].
cbn [pe_to sexpr_has_agg]; induction l as [ | x l IHl]; [reflexivity | simpl; rewrite IH; exact IHl].
Qed.

Lemma sitems_no_agg : forall sa k es, (forall e, In e es -> sexpr_has_agg ORN basesort nil sa e = false) ->
  sselect_has_agg ORN basesort nil sa (S_List (sitems k es)) = false.
Proof.
intros sa k es; revert k; induction es as [ | e es IH]; intros k H; [reflexivity | ].
cbn [sitems sselect_has_agg existsb]; rewrite (H e (or_introl eq_refl)); cbn [orb].
apply (IH (S k)); intros x Ix; apply H; right; exact Ix.
Qed.

Lemma sitems_rows : forall F k es,
  map (fun it => match it with S_As e a => (a, ev F e) end) (sitems k es) = pairs k (map (ev F) es).
Proof. intros F k es; revert k; induction es as [ | e es IH]; intro k; [reflexivity | simpl; f_equal; apply IH]. Qed.

Lemma psel_rows : forall es lf' c, (forall sa e, In e es -> sexpr_has_agg ORN basesort nil sa e = false) ->
  (forall t, er (slice_t T relname t :: nil) c = false) ->
  eq0 (psel es lf' c) =
  map (fun t => mk_row O (pairs 0 (map (ev (slice_t T relname t :: nil)) es)))
      (filter (fun t => is_true3 T (ec (slice_t T relname t :: nil) c))
              (fold_left (fun l1 l2 => cross_product T l1 l2) (map ef0 lf') (empty_tuple T :: nil))).
Proof.
intros es lf' c Ha Hc; unfold psel.
rewrite (full_select_rows_R T relname ORN O basesort instance Herr nil lf' _ c Hc).
2: { intro sa; apply sitems_no_agg; intros e Ie; apply Ha; exact Ie. }
apply map_ext; intro t; cbn [row_of_R]; rewrite sitems_rows; reflexivity.
Qed.


(** * Renamings and products *)

Lemma snd_shiftp : forall n i off, map (@snd _ _) (shiftp i off n) = map (fun j => pa (off + j)) (seq i n).
Proof. intro n; induction n as [ | n IH]; intros i off; [reflexivity | simpl; f_equal; apply IH]. Qed.

Lemma find_shift : forall n i off j, i <= j < i + n ->
  Oset.find (OAtt T) (pa (off + j)) (map (fun x => (snd x, fst x)) (shiftp i off n)) = Some (pa j).
Proof.
intro n; induction n as [ | n IH]; intros i off j L; [lia | ].
cbn [shiftp map fst snd]; rewrite find_cons.
destruct (Oset.eq_bool (OAtt T) (pa (off + j)) (pa (off + i))) eqn:E.
- rewrite Oset.eq_bool_true_iff in E; apply Hpa in E; replace j with i by lia; reflexivity.
- apply IH; destruct (Nat.eq_dec i j) as [D | D]; [subst; rewrite Oset.eq_bool_refl in E; discriminate E | lia].
Qed.

Lemma rename_inv : forall off n t,
  labels T (SqlFull.rename_tuple O (Ren_List T (shiftp 0 off n)) t) =S= rangeS off n /\
  readat off n (SqlFull.rename_tuple O (Ren_List T (shiftp 0 off n)) t) = readat 0 n t.
Proof.
intros off n t; cbn [SqlFull.rename_tuple]; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)), snd_shiftp; unfold rangeS; rewrite (map_seq_shift _ pa off n).
  apply Fset.equal_refl.
- unfold readat; apply map_ext_in; intros j Ij; rewrite in_seq in Ij; rewrite dot_mk_tuple.
  replace (Fset.mem (A T) (pa (off + j)) (Fset.mk_set (A T) (map snd (shiftp 0 off n)))) with true.
  + rewrite (find_shift n 0 off j) by lia; apply store_id.
  + symmetry; rewrite snd_shiftp, <- (map_seq_shift _ pa off n); fold (rangeS off n); rewrite mem_range.
    apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia.
Qed.

Lemma ef_ren : forall q' rho, ef0 (Fr_Query q' rho) = map (SqlFull.rename_tuple O rho) (eq0 q').
Proof.
intros q' rho; change (ef0 (Fr_Query q' rho)) with
  (map (fun t => let t' := SqlFull.rename_tuple O rho t in
                 if row_error O t && negb (row_error O t') then err_row O t' else t') (eq0 q')).
apply map_ext; intro t; cbv zeta; rewrite (row_error_false T O Herr); reflexivity.
Qed.

Lemma join_inv : forall off n x y, labels T x =S= rangeS 0 off -> labels T y =S= rangeS off n ->
  labels T (join_tuple T x y) =S= rangeS 0 (off + n) /\
  readat 0 (off + n) (join_tuple T x y) = readat 0 off x ++ readat off n y.
Proof.
intros off n x y Hx Hy; split.
- unfold join_tuple; rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
  rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.union_eq _ _ _ _ _ Hx Hy)).
  exact (range_union 0 off n).
- unfold readat; rewrite seq_app, map_app; f_equal.
  + apply map_ext_in; intros j Ij; rewrite in_seq in Ij; unfold join_tuple; rewrite dot_mk_tuple.
    rewrite Fset.mem_union, (Fset.mem_eq_2 _ _ _ Hx), mem_range.
    replace ((0 <=? 0 + j) && (0 + j <? 0 + off)) with true by (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
    reflexivity.
  + rewrite map_seq_shift; apply map_ext_in; intros j Ij; rewrite in_seq in Ij; unfold join_tuple; rewrite dot_mk_tuple.
    rewrite Fset.mem_union, (Fset.mem_eq_2 _ _ _ Hx), (Fset.mem_eq_2 _ _ _ Hy), !mem_range.
    replace ((0 <=? 0 + (0 + off + j)) && (0 + (0 + off + j) <? 0 + off)) with false
      by (symmetry; apply andb_false_iff; right; apply Nat.ltb_ge; lia).
    replace ((off <=? 0 + (0 + off + j)) && (0 + (0 + off + j) <? off + n)) with true
      by (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
    cbn [orb]; f_equal; f_equal; lia.
Qed.

Lemma F2_map : forall (X Y X' Y' : Type) (P : X -> Y -> Prop) (Q : X' -> Y' -> Prop) f g l1 l2,
  Forall2 P l1 l2 -> (forall a b, P a b -> Q (f a) (g b)) -> Forall2 Q (map f l1) (map g l2).
Proof. intros X Y X' Y' P Q f g l1 l2 H K; induction H; constructor; auto. Qed.

Lemma F2_flat_map : forall (X Y X' Y' : Type) (P : X -> Y -> Prop) (Q : X' -> Y' -> Prop) f g l1 l2,
  Forall2 P l1 l2 -> (forall a b, P a b -> Forall2 Q (f a) (g b)) -> Forall2 Q (flat_map f l1) (flat_map g l2).
Proof. intros X Y X' Y' P Q f g l1 l2 H K; induction H; [constructor | simpl; apply Forall2_app; auto]. Qed.

Lemma F2_filter : forall (X Y : Type) (P : X -> Y -> Prop) p r l1 l2,
  Forall2 P l1 l2 -> (forall a b, P a b -> p a = r b) -> Forall2 P (filter p l1) (filter r l2).
Proof.
intros X Y P p r l1 l2 H K; induction H as [ | a b l1 l2 Hab H IH]; [constructor | simpl].
rewrite (K a b Hab); destruct (r b); [constructor; assumption | exact IH].
Qed.

Definition Inv n t row := labels T t =S= rangeS 0 n /\ readat 0 n t = row.

(** the invariant holds up to the equality of tuples *)
Lemma Inv_teq : forall n t' t row, t' =t= t -> Inv n t row -> Inv n t' row.
Proof.
intros n t' t row H [L R]; rewrite tuple_eq in H; destruct H as [Hl Hd]; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ Hl); exact L.
- rewrite <- R; unfold readat; apply map_ext_in; intros j Hj; apply Hd.
  rewrite (Fset.mem_eq_2 _ _ _ Hl), (Fset.mem_eq_2 _ _ _ L), mem_range; rewrite in_seq in Hj.
  apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia.
Qed.

Lemma Inv_unify : forall n atts rows l, Forall2 (Inv n) rows l -> Forall2 (Inv n) (unify_rows O atts rows) l.
Proof.
intros n atts rows l H; assert (U := SqlRelate.unify_rows_eq T O Hun atts rows).
revert l H; induction U as [ | x y l1 l2 Hxy U IH]; intros l H; inversion H; subst; constructor.
- apply (Inv_teq _ _ _ _ Hxy); assumption.
- apply IH; assumption.
Qed.

Lemma prod_inv : forall lf off acc accp, Forall2 (Inv off) acc accp ->
  (forall q, In q lf -> Forall2 (Inv (parity q)) (eq0 (pq_to q)) (peval q)) ->
  Forall2 (Inv (off + fold_right (fun q n => parity q + n) 0 lf))
    (fold_left (fun l1 l2 => cross_product T l1 l2) (map ef0 (pfrom off lf)) acc)
    (fold_left (fun acc l => flat_map (fun x => map (fun y => x ++ y) l) acc) (map peval lf) accp).
Proof.
intro lf; induction lf as [ | q lf IHl]; intros off acc accp Ha Hq.
- cbn [fold_right]; rewrite Nat.add_0_r; exact Ha.
- cbn [pfrom map fold_left fold_right]; rewrite Nat.add_assoc; apply IHl.
  + unfold cross_product; apply (F2_flat_map _ _ _ _ (Inv off)); [exact Ha | ].
    intros x row [Lx Rx]; rewrite ef_ren, map_map.
    apply (F2_map _ _ _ _ (Inv (parity q))); [apply Hq; left; reflexivity | ].
    intros t r [Lt Rt]; destruct (rename_inv off (parity q) t) as [L1 R1].
    destruct (join_inv off (parity q) x _ Lx L1) as [L2 R2].
    split; [exact L2 | rewrite R2, R1, Rx, Rt; reflexivity].
  + intros q' I; apply Hq; right; exact I.
Qed.


(** * The sorts *)

Lemma sitems_att : forall k es, map (@sitem_att T relname) (sitems k es) = map pa (seq k (length es)).
Proof. intros k es; revert k; induction es as [ | e es IH]; intro k; [reflexivity | simpl; f_equal; apply IH]. Qed.

Lemma range_0 : forall k, rangeS k 0 =S= Fset.empty (A T).
Proof. intro k; unfold rangeS; rewrite Fset.equal_spec; intro x; rewrite Fset.mem_mk_set, Fset.empty_spec; reflexivity. Qed.

Lemma pfrom_sort : forall lf off,
  Fset.Union (A T) (map (sfrom_sort ORN basesort nil) (pfrom off lf)) =S= rangeS off (fold_right (fun q n => parity q + n) 0 lf).
Proof.
intro lf; induction lf as [ | q lf IH]; intro off; rewrite Fset.equal_spec; intro x.
- cbn [pfrom map fold_right]; rewrite Fset.Union_unfold, Fset.empty_spec; unfold rangeS; rewrite Fset.mem_mk_set; reflexivity.
- cbn [pfrom map fold_right]; rewrite Fset.Union_unfold, Fset.mem_union, (Fset.mem_eq_2 _ _ _ (IH (off + parity q))).
  cbn [sfrom_sort]; rewrite snd_shiftp, <- (map_seq_shift _ pa off); fold (rangeS off (parity q)).
  rewrite <- Fset.mem_union; apply Fset.mem_eq_2, range_union.
Qed.

Lemma pq_sort : forall q, squery_sort ORN basesort nil (pq_to q) =S= rangeS 0 (parity q).
Proof.
fix IH 1; intro q; rewrite pq_to_unfold; destruct q as [r | items lf w | lf w | q1 q2]; cbn [parity].
- unfold psel; cbn [squery_sort sspec_sort]; rewrite sitems_att, !map_length; apply Fset.equal_refl.
- unfold psel; cbn [squery_sort sspec_sort]; rewrite sitems_att, !map_length; apply Fset.equal_refl.
- cbn [squery_sort sspec_sort]; apply pfrom_sort.
- cbn [squery_sort]; apply IH.
Qed.

(** * The rows *)

Lemma F2_same : forall (X Y Z : Type) (P : Y -> Z -> Prop) (f : X -> Y) (g : X -> Z) l,
  (forall x, In x l -> P (f x) (g x)) -> Forall2 P (map f l) (map g l).
Proof. intros X Y Z P f g l H; induction l as [ | x l IH]; constructor; [apply H; left; reflexivity | apply IH; intros; apply H; right; assumption]. Qed.

Lemma filter_all : forall (X : Type) (l : list X), filter (fun _ => true) l = l.
Proof. intros X l; induction l as [ | x l IH]; [reflexivity | simpl; f_equal; exact IH]. Qed.

Lemma inv_empty : Forall2 (Inv 0) (empty_tuple T :: nil) (nil :: nil).
Proof.
constructor; [ | constructor]; split; [ | reflexivity].
rewrite (Fset.equal_eq_1 _ _ _ _ (labels_empty_tuple T)), Fset.equal_spec; intro x.
rewrite Fset.empty_spec; unfold rangeS; rewrite Fset.mem_mk_set; reflexivity.
Qed.

Lemma row_inv : forall N t row es, Inv N t row ->
  Inv (length es) (mk_row O (pairs 0 (map (ev (slice_t T relname t :: nil)) (map pe_to es))))
      (map (pe_eval row) es).
Proof.
intros N t row es [Lt Rt]; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_row_pairs _)), !map_length; apply Fset.equal_refl.
- rewrite <- (map_length pe_to es), <- (map_length (ev (slice_t T relname t :: nil)) (map pe_to es)), read_mk_row.
  rewrite map_map; apply map_ext; intro e; rewrite (pe_agree N t Lt), Rt; reflexivity.
Qed.

Lemma ren_star_id : forall l, map (SqlFull.rename_tuple O (Ren_Star T)) l = l.
Proof. intro l; induction l as [ | x l IH]; [reflexivity | simpl; rewrite IH; reflexivity]. Qed.

Theorem positional_agree : forall q, Forall2 (Inv (parity q)) (eq0 (pq_to q)) (peval q).
Proof.
fix IH 1; intro q; rewrite pq_to_unfold.
assert (HL : forall lf, Forall2 (Inv (fold_right (fun q n => parity q + n) 0 lf))
                      (fold_left (fun l1 l2 => cross_product T l1 l2) (map ef0 (pfrom 0 lf)) (empty_tuple T :: nil))
                      (pprod (map peval lf))).
{ intro lf; apply (prod_inv lf 0 _ _ inv_empty).
  induction lf as [ | q1 lf IHl]; intros q' I; [contradiction I | destruct I as [<- | I]; [apply IH | apply IHl; exact I]]. }
destruct q as [r | items lf w | lf w | q1 q2].
- rewrite psel_rows.
  2: { intros sa e Ie; rewrite in_map_iff in Ie; destruct Ie as [a [<- _]]; reflexivity. }
  2: { intro t; reflexivity. }
  cbn [map fold_left peval parity].
  replace (filter _ (cross_product T (empty_tuple T :: nil) (ef0 (Fr_Query (SQ_Table T r) (Ren_Star T)))))
    with (map (join_tuple T (empty_tuple T)) (Febag.elements _ (instance r))).
  2: { rewrite ef_ren, ren_star_id.
       change (eq0 (SQ_Table T r)) with (Febag.elements _ (instance r)).
       unfold cross_product; cbn [flat_map]; rewrite app_nil_r.
       symmetry; induction (map (join_tuple T (empty_tuple T)) (Febag.elements _ (instance r))) as [ | x l IHl]; [reflexivity | ].
       cbn [filter]; rewrite true_is_true, IHl; reflexivity. }
  rewrite map_map.
  apply F2_same; intros t It; split.
  + rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_row_pairs _)), !map_length; apply Fset.equal_refl.
  + rewrite <- (map_length (E_Col T relname) ({{{basesort r}}})),
      <- (map_length (ev (slice_t T relname (join_tuple T (empty_tuple T) t) :: nil)) (map (E_Col T relname) _)), read_mk_row, map_map.
    apply map_ext_in; intros a Ia; cbn [eval_sexpr]; unfold is_hidden; cbn [lookup slice_t].
    assert (Ma : a inS labels T t)
      by (rewrite (Fset.mem_eq_2 _ _ _ (Hinst r t It)); apply Fset.in_elements_mem; exact Ia).
    unfold join_tuple; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Fset.mem_union, Ma, orb_true_r, dot_mk_tuple.
    rewrite Fset.mem_union, Ma, orb_true_r, (Fset.mem_eq_2 _ _ _ (labels_empty_tuple T)), Fset.empty_spec; reflexivity.
- rewrite psel_rows.
  2: { intros sa e Ie; rewrite in_map_iff in Ie; destruct Ie as [p [<- _]]; apply pe_no_agg. }
  2: { intro t; apply pc_noraise. }
  cbn [peval parity]; rewrite <- (map_map (@snd _ _) pe_to), <- (map_length (@snd _ _) items).
  rewrite (map_ext (fun row => map (fun p => pe_eval row (snd p)) items) (fun row => map (pe_eval row) (map (@snd _ _) items)))
    by (intro row; rewrite map_map; reflexivity).
  apply (F2_map _ _ _ _ (Inv (fold_right (fun q n => parity q + n) 0 lf))).
  + apply F2_filter; [apply HL | ].
    intros t row [Lt Rt]; rewrite (proj1 (pc_agree _ t Lt w)), Rt; reflexivity.
  + intros t row H; apply (row_inv _ t row _ H).
- rewrite (full_select_rows_R T relname ORN O basesort instance Herr nil _ (S_Star T relname) _ (fun t => pc_noraise t w) (fun _ => eq_refl)).
  cbn [row_of_R peval parity]; rewrite map_id.
  apply F2_filter; [apply HL | ].
  intros t row [Lt Rt]; rewrite (proj1 (pc_agree _ t Lt w)), Rt; reflexivity.
  intros; reflexivity.
- change (eq0 (SQ_Set Union Set_All (pq_to q1) (pq_to q2))) with
    (if Fset.equal (A T) (squery_sort ORN basesort nil (pq_to q1)) (squery_sort ORN basesort nil (pq_to q2))
     then unify_rows O ({{{squery_sort ORN basesort nil (pq_to q1)}}})
            (keep_errors O (eval_set_op O Union Set_All (eq0 (pq_to q1)) (eq0 (pq_to q2))) (eq0 (pq_to q1) ++ eq0 (pq_to q2)))
     else nil).
  rewrite (Fset.equal_eq_1 _ _ _ _ (pq_sort q1)), (Fset.equal_eq_2 _ _ _ _ (pq_sort q2)), range_equal.
  cbn [peval parity]; destruct (Nat.eqb (parity q1) (parity q2)) eqn:E; [ | constructor].
  apply Inv_unify; rewrite (keep_errors_id T O Herr); cbn [eval_set_op]; apply Forall2_app; [apply IH | ].
  apply Nat.eqb_eq in E; rewrite E; apply IH.
Qed.

(** the rows of the compiled query, read by position, are the rows of the positional semantics *)
Corollary positional_rows : forall q, map (readat 0 (parity q)) (eq0 (pq_to q)) = peval q.
Proof.
intro q; generalize (positional_agree q); intro H; induction H as [ | t row l1 l2 [_ R] H IH]; [reflexivity | ].
simpl; rewrite R, IH; reflexivity.
Qed.

End Sec.
