(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**        The query language of SqlFull over the values of NullValues              *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String ZArith NArith QArith Qcanon.

Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.

Import Tuple.
Require Import Values TuplesImpl GenericInstance SqlSyntax.

Close Scope Q_scope.
Close Scope Qc_scope.

(** * Dialects

    What SqlFull needs to know about the values of NullValues, for a dialect which, like
    PostgreSQL, compares strings byte by byte and puts the NULLs last. *)

Definition TNull_PostgreSQL : dialect TNull :=
  mk_dialect TNull
             NullValues.is_null
             (NullValues.Value_Z None)
             NullValues.bool3_of_value
             NullValues.value_of_bool3
             NullValues.sql_eq3
             NullValues.sql_order
             (fun z => NullValues.Value_Z (Some z))
             NullValues.rat_of_value
             NullValues.value_of_rat
             (fun v => v)
             false
             (fun _ => true)
             (fun _ => true) (fun _ => true) (fun _ => true)
             NullValues.is_err NullValues.Value_Err (Attr_string "#error")
             NullValues.is_lazy_symbol (fun _ _ => false) false.

Definition TNull_ops := TNull_PostgreSQL.

(** * Evaluation in a database state *)

Definition eval_squery_in_state (db : db_state) (q : squery TNull relname) :=
  eval_query_list ORN TNull_ops (_basesort _ db) (_instance _ db) q.

Definition show_squery_in_state (db : db_state) (q : squery TNull relname) :=
  List.map (show_tuple TNull) (eval_squery_in_state db q).

(** * Checking results

    A result is checked against the rows which are expected, each row being given
    as a list of values, in the order of the attributes [atts]. *)

Definition row_of (atts : list attribute) (t : tuple TNull) := List.map (dot TNull t) atts.

Definition values_eqb (l1 l2 : list NullValues.value) :=
  Oset.eq_bool (mk_olists NullValues.OVal) l1 l2.

Fixpoint rows_eqb (l1 l2 : list (list NullValues.value)) :=
  match l1, l2 with
  | nil, nil => true
  | r1 :: l1, r2 :: l2 => andb (values_eqb r1 r2) (rows_eqb l1 l2)
  | _, _ => false
  end.

Fixpoint remove_row (r : list NullValues.value) (l : list (list NullValues.value)) :=
  match l with
  | nil => None
  | r' :: l => if values_eqb r r' then Some l 
               else match remove_row r l with
                    | Some l' => Some (r' :: l')
                    | None => None
                    end
  end.

Fixpoint rows_permb (l1 l2 : list (list NullValues.value)) :=
  match l1 with
  | nil => match l2 with nil => true | _ => false end
  | r :: l1 => match remove_row r l2 with
               | Some l2' => rows_permb l1 l2'
               | None => false
               end
  end.

Definition sort_is db q (atts : list attribute) :=
  Fset.equal (A TNull) (sort_of_query ORN (_basesort _ db) q) (Fset.mk_set (A TNull) atts).

(** The result of [q] is exactly the list [rows]: for queries with an ORDER BY. *)
Definition returns_list db q atts rows :=
  let res := eval_squery_in_state db q in
  andb (forallb (fun t => Fset.equal (A TNull) (labels TNull t) (Fset.mk_set (A TNull) atts)) res)
       (rows_eqb (List.map (row_of atts) res) rows).

(** The result of [q] is the bag [rows]. *)
Definition returns_bag db q atts rows :=
  let res := eval_squery_in_state db q in
  andb (forallb (fun t => Fset.equal (A TNull) (labels TNull t) (Fset.mk_set (A TNull) atts)) res)
       (rows_permb (List.map (row_of atts) res) rows).

(** * Shorthands for the syntax *)

Notation sexpr := (sexpr TNull relname).
Notation scond := (scond TNull relname).
Notation squery := (squery TNull relname).
Notation sfrom := (sfrom TNull relname).
Notation sitem := (sitem TNull relname).

Definition VZ (z : Z) := NullValues.Value_Z (Some z).
Definition VS (s : string) := NullValues.Value_string (Some s).
Definition VB (b : bool) := NullValues.Value_bool (Some b).
Definition VQ (n : Z) (d : positive) := NullValues.Value_Q (Some (Q2Qc (Qmake n d))).
Definition NullZ := NullValues.Value_Z None.
Definition NullS := NullValues.Value_string None.
Definition NullB := NullValues.Value_bool None.
Definition NullQ := NullValues.Value_Q None.

Definition col (a : attribute) : sexpr := @E_Col TNull relname a.
Definition cst (v : NullValues.value) : sexpr := @E_Const TNull relname v.
Definition int (z : Z) : sexpr := cst (VZ z).
Definition str (s : string) : sexpr := cst (VS s).
Definition fn (f : string) (l : list sexpr) : sexpr := 
  @E_Fun TNull relname (Symbol f) l.
Definition c_true : scond := @C_True TNull relname.
Definition agg (f : string) (e : sexpr) : sexpr := 
  @E_Agg TNull relname (Aggregate f) Set_All e c_true.
Definition agg_distinct (f : string) (e : sexpr) : sexpr := 
  @E_Agg TNull relname (Aggregate f) Set_Distinct e c_true.
Definition agg_filter (f : string) (e : sexpr) (c : scond) : sexpr := 
  @E_Agg TNull relname (Aggregate f) Set_All e c.
Definition count_star : sexpr := agg "count(*)" (int 1).
Definition e_case (c : scond) (e1 e2 : sexpr) : sexpr := @E_Case TNull relname c e1 e2.
Definition e_cond (c : scond) : sexpr := @E_Cond TNull relname c.
Definition e_sub (q : squery) : sexpr := @E_Sub TNull relname q.
Definition pred (p : string) (l : list sexpr) : scond := 
  @C_Pred TNull relname (Predicate p) l.
Definition c_and (c1 c2 : scond) : scond := @C_Conj TNull relname And_F c1 c2.
Definition c_or (c1 c2 : scond) : scond := @C_Conj TNull relname Or_F c1 c2.
Definition c_not (c : scond) : scond := @C_Not TNull relname c.
Definition c_expr (e : sexpr) : scond := @C_Expr TNull relname e.
Definition c_exists (q : squery) : scond := @C_Exists TNull relname q.
Definition c_in (l : list sexpr) (q : squery) (la : list attribute) : scond := 
  @C_In TNull relname l q la.
Definition c_any (p : string) (l : list sexpr) (q : squery) (la : list attribute) : scond := 
  @C_Quant TNull relname Exists_F (Predicate p) l q la.
Definition c_all (p : string) (l : list sexpr) (q : squery) (la : list attribute) : scond := 
  @C_Quant TNull relname Forall_F (Predicate p) l q la.
Definition as_ (e : sexpr) (a : attribute) : sitem := @S_As TNull relname e a.
Definition table (r : string) : squery := @SQ_Table TNull relname (Rel r).
Definition from_query (q : squery) : sfrom := @Fr_Query TNull relname q (Ren_Star TNull).
Definition from_table (r : string) : sfrom := from_query (table r).
Definition from_as (q : squery) (l : list (attribute * attribute)) : sfrom := 
  @Fr_Query TNull relname q (Ren_List TNull l).
Definition join (jt : join_type) (f1 f2 : sfrom) (c : scond) : sfrom := 
  @Fr_Join TNull relname jt false f1 f2 c.
Definition join_lateral (jt : join_type) (f1 f2 : sfrom) (c : scond) : sfrom := 
  @Fr_Join TNull relname jt true f1 f2 c.
Definition g_fine := @G_Fine TNull relname.
Definition g_by (l : list sexpr) := @G_By TNull relname l.
Definition g_sets (l : list (list sexpr)) := @G_Sets TNull relname l.
Definition g_rollup (l : list sexpr) := @G_Rollup TNull relname l.
Definition g_cube (l : list sexpr) := @G_Cube TNull relname l.
Definition grouping (e : sexpr) : sexpr := @E_Grouping TNull relname e.
Definition s_star := @S_Star TNull relname.
Definition s_list (l : list sitem) := @S_List TNull relname l.

(** [SELECT [DISTINCT] s FROM lf WHERE c GROUP BY g HAVING h] *)
Definition select_full sq s lf c g h : squery := 
  @SQ_Select TNull relname (@Select TNull relname sq s lf c g h).

(** [SELECT items FROM froms WHERE c] *)
Definition select_where (l : list sitem) (lf : list sfrom) (c : scond) : squery :=
  select_full Set_All (s_list l) lf c g_fine c_true.

Definition select_distinct (l : list sitem) (lf : list sfrom) (c : scond) : squery :=
  select_full Set_Distinct (s_list l) lf c g_fine c_true.

(** [SELECT * FROM froms WHERE c] *)
Definition select_star_where (lf : list sfrom) (c : scond) : squery :=
  select_full Set_All s_star lf c g_fine c_true.

(** [SELECT items FROM froms WHERE c GROUP BY g HAVING h] *)
Definition select_group (l : list sitem) (lf : list sfrom) (c : scond) 
           (g : list sexpr) (h : scond) : squery :=
  select_full Set_All (s_list l) lf c (g_by g) h.

(** the same, with any grouping *)
Definition select_grouped (l : list sitem) (lf : list sfrom) (g : sgroup TNull relname) : squery :=
  select_full Set_All (s_list l) lf c_true g c_true.

Definition set_op_ (o : set_op) (sq : set_quantifier) (q1 q2 : squery) : squery := 
  @SQ_Set TNull relname o sq q1 q2.
Definition o_by (e : sexpr) (d : order_dir) := @O_By TNull relname e d Nulls_Default.
Definition o_by_nulls (e : sexpr) (d : order_dir) (n : nulls_order) := @O_By TNull relname e d n.
Definition order_by (q : squery) lo : squery := @SQ_Order TNull relname q lo None None.
Definition order_limit (q : squery) lo (off lim : option N) : squery := 
  @SQ_Order TNull relname q lo off lim.
Definition fetch_first (q : squery) lo (off : option N) (ties percent : bool) (n : N) : squery :=
  @SQ_Fetch TNull relname q lo off ties percent n.
Definition agg_x (f : string) (e : sexpr) (sep : option sexpr) lo : sexpr :=
  @E_AggX TNull relname (Aggregate f) Set_All e sep lo c_true.
Definition with_ (r : string) (q1 q2 : squery) : squery := @SQ_With TNull relname (Rel r) q1 q2.
Definition with_rec (sq : set_quantifier) (r : string) (q1 q2 q3 : squery) : squery := @SQ_WithRec TNull relname sq (Rel r) q1 q2 q3.
Definition window (q : squery) lw : squery := @SQ_Window TNull relname q lw.
Definition w_as f (lp : list sexpr) lo (a : attribute) := @W_As TNull relname f lp lo a.
Definition w_agg (f : string) (e : sexpr) (fr : frame) := 
  @W_Agg TNull relname (Aggregate f) Set_All e fr.
Definition w_row_number := @W_Row_Number TNull relname.
Definition w_rank := @W_Rank TNull relname.
Definition w_dense_rank := @W_Dense_Rank TNull relname.
Definition w_ntile n := @W_Ntile TNull relname n.
Definition w_percent_rank := @W_Percent_Rank TNull relname.
Definition w_cume_dist := @W_Cume_Dist TNull relname.
Definition w_lag (e : sexpr) n (d : sexpr) := @W_Lag TNull relname e n d.
Definition w_lead (e : sexpr) n (d : sexpr) := @W_Lead TNull relname e n d.
Definition w_first_value (e : sexpr) fr := @W_First_Value TNull relname e fr.
Definition w_last_value (e : sexpr) fr := @W_Last_Value TNull relname e fr.
Definition w_nth_value (e : sexpr) n fr := @W_Nth_Value TNull relname e n fr.
Definition values_ (la : list attribute) (rows : list (list sexpr)) : squery := 
  @SQ_Values TNull relname la rows.

(** [f1 NATURAL JOIN f2], when [la] is the list of the attributes which are common
    to [f1] and [f2], and [lb] a list of fresh names for these attributes in [f2],
    [rest] being the other attributes of [f2]: the common attributes of [f2] are 
    renamed, and equated with those of [f1]. As a NULL is not equal to a NULL, this 
    is not the join of the tuples which agree on their common attributes. *)
Definition from_natural_join (f1 : sfrom) (q2 : squery) 
           (la lb rest : list attribute) : sfrom :=
  join J_Inner f1 
          (from_as q2 (List.combine la lb ++ List.map (fun a => (a, a)) rest))
          (C_And_N (List.map (fun ab => pred "=" (col (fst ab) :: col (snd ab) :: nil))
                             (List.combine la lb))).

(** [SELECT DISTINCT ON (keys) cols FROM q ORDER BY lo]: the first row of each group of [keys]
    in the order [lo], computed with [ROW_NUMBER] ([rn] must be a fresh attribute).
    The result of [DISTINCT ON] without a final [ORDER BY] is not ordered; the ties of [lo] are
    resolved as in the sort of the window, as in the engines (which leave the choice open). *)
Definition distinct_on (q : squery) (cols : list attribute) (keys : list sexpr) lo (rn : attribute) : squery :=
  select_where (map (fun a => as_ (col a) a) cols)
               (from_query (window q (w_as w_row_number keys lo rn :: nil)) :: nil)
               (pred "=" (col rn :: int 1 :: nil)).

