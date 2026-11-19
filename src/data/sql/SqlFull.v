(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**           An executable semantics for the query language of SQL                 *)
(**                                                                                 *)
(************************************************************************************)

(** * SqlFull: the query fragment of SQL

    [Sql.v] formalises SELECT-FROM-WHERE-GROUP BY-HAVING blocks combined with bag
    set operations, and is the fragment which is proven equivalent to the
    extended relational algebra of [SqlAlgebra.v]. This file is a strict
    extension of its _syntax_ and of its _semantics_, which aims at covering the
    whole query language (DQL) of SQL:

<<
 query ::= table
         | query { UNION | INTERSECT | EXCEPT } [ ALL | DISTINCT ] query
         | SELECT [ ALL | DISTINCT ] { * | expr AS name, ... }
             FROM from_item, ...
             [ WHERE cond ] [ GROUP BY expr, ... ] [ HAVING cond ]
         | query [ ORDER BY expr [ ASC | DESC ] [ NULLS { FIRST | LAST } ], ... ]
                 [ OFFSET n ] [ LIMIT n ]
         | SELECT *, wfun OVER (PARTITION BY ... ORDER BY ... frame) AS name, ...
             FROM query
         | WITH name AS (query) query

 from_item ::= query [ AS (old AS new, ...) ]
             | from_item [ INNER | LEFT | RIGHT | FULL ] JOIN [ LATERAL ] from_item
                 ON cond

 expr ::= constant | column | f (expr, ...)
        | agg ([ ALL | DISTINCT ] expr) [ FILTER (WHERE cond) ]
        | CASE WHEN cond THEN expr ELSE expr END
        | cond                      -- a condition, as a boolean value
        | ( query )                 -- scalar subquery

 cond ::= cond AND cond | cond OR cond | NOT cond | TRUE
        | p (expr, ...)             -- =, <, IS NULL, LIKE, BETWEEN, ...
        | expr                      -- a boolean expression, as a condition
        | expr op { ANY | ALL } ( query )
        | (expr, ...) IN ( query )
        | EXISTS ( query )
>>

    As in the rest of the library, tuples are _named_: a tuple is a finite map
    from attributes to values, and the attributes of the items of a FROM clause
    are expected to be pairwise distinct (table aliases are modelled by
    attribute renamings).

    The semantics is a total function: the runtime errors of SQL (division by
    zero, a scalar subquery returning several rows, an invalid cast) are
    modelled by NULL.
*)

Set Implicit Arguments.

Require Import Relations SetoidList List String Ascii Bool ZArith NArith QArith.

Require Import BasicFacts ListFacts ListPermut ListSort OrderedSet
        FiniteSet FiniteBag FiniteCollection Join FlatData Tree Bool3 Formula
        Partition.

Close Scope Q_scope.

(** * Syntax which does not depend on the data model *)

(** ALL or DISTINCT, for SELECT, for set operations and for aggregates. *)
Inductive set_quantifier : Type :=
  | Set_All
  | Set_Distinct.

Inductive join_type : Type :=
  | J_Inner   (** [INNER JOIN]; [CROSS JOIN] is [INNER JOIN ... ON TRUE] *)
  | J_Left    (** [LEFT OUTER JOIN] *)
  | J_Right   (** [RIGHT OUTER JOIN] *)
  | J_Full.   (** [FULL OUTER JOIN] *)

Inductive order_dir : Type :=
  | Asc
  | Desc.

Inductive nulls_order : Type :=
  | Nulls_Default  (** NULLs are larger than any other value, as in PostgreSQL and Oracle *)
  | Nulls_First
  | Nulls_Last.

(** Bounds of a window frame. *)
Inductive frame_bound : Type :=
  | Unbounded_Preceding
  | Preceding : nat -> frame_bound
  | Current_Row
  | Following : nat -> frame_bound
  | Unbounded_Following.

(** Window frames. In [ROWS] mode, offsets count rows; in [GROUPS] mode they
    count groups of peers (rows which are equal w.r.t. the ORDER BY of the
    window). A [RANGE] frame whose bounds are [UNBOUNDED PRECEDING],
    [CURRENT ROW] or [UNBOUNDED FOLLOWING] is the [GROUPS] frame with the same
    bounds. In [RANGE] mode with offsets, the frame is made of the rows whose (single) ORDER BY key
    is within the offsets of the key of the current row; the NULL keys are peers of each other and
    of nothing else, and the offsets are integers. *)
Inductive frame : Type :=
  | Frame_Rows : frame_bound -> frame_bound -> frame
  | Frame_Groups : frame_bound -> frame_bound -> frame
  | Frame_Range : frame_bound -> frame_bound -> frame.

(** The frame which SQL uses when none is given:
    [RANGE BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW]. Without ORDER BY, all
    the rows of the partition are peers, and this is the whole partition. *)
Definition default_frame := Frame_Groups Unbounded_Preceding Current_Row.

Definition whole_partition := Frame_Rows Unbounded_Preceding Unbounded_Following.

Section Sec.

Hypothesis T : Tuple.Rcd.

Hypothesis relname : Type.
Hypothesis ORN : Oset.Rcd relname.

Import Tuple.

Notation predicate := (Tuple.predicate T).
Notation symb := (Tuple.symbol T).
Notation aggregate := (Tuple.aggregate T).
Notation value := (value T).
Notation attribute := (attribute T).
Notation tuple := (tuple T).
Notation setA := (Fset.set (A T)).
Notation BTupleT := (Fecol.CBag (CTuple T)).
Notation bagT := (Febag.bag BTupleT).
Notation bool3 := (Bool.b (B T)).

(** * Dialects

    SQL is a family of languages. What is common to all of them is the structure of
    the queries and the three-valued logic; they differ by what is a value and by
    the way values are compared and combined (the instance [Tuple.Rcd], see
    [Values.v] and [Dialects.v]), and by the few aspects of the evaluation of
    queries which are recorded here. The record [dialect] gathers what the constructs
    of this file need to know. *)

(** The constructs of the language which are not supported by all the dialects. *)
Inductive feature : Type :=
  | F_Right_Join
  | F_Full_Join
  | F_Lateral
  | F_Intersect
  | F_Except
  (** [INTERSECT ALL] and [EXCEPT ALL] *)
  | F_Intersect_All
  | F_Except_All
  | F_Window
  (** window frames in [GROUPS] mode *)
  | F_Frame_Groups
  (** [agg(...) FILTER (WHERE ...)] *)
  | F_Filter_Agg
  (** [NULLS FIRST] and [NULLS LAST] in [ORDER BY] *)
  | F_Nulls_Order
  (** [e op ANY (q)], [e op ALL (q)] *)
  | F_Any_All
  | F_With
  (** [WITH RECURSIVE] *)
  | F_Recursive
  (** [GROUPING SETS], [ROLLUP], [CUBE] *)
  | F_Grouping_Sets
  | F_Rollup
  | F_Cube
  (** a column which is neither grouped nor in an aggregate, in a block with aggregates or a [GROUP BY]
      (rejected by [ONLY_FULL_GROUP_BY], by PostgreSQL and by Oracle; SQLite takes the value of a row) *)
  | F_Bare_Column
  (** [FETCH FIRST n ROWS WITH TIES] *)
  | F_Fetch_Ties
  (** [FETCH FIRST p PERCENT ROWS ONLY] *)
  | F_Fetch_Percent
  (** a condition used as a value, or a value used as a condition (booleans) *)
  | F_Cond_Value
  (** [(e1, ..., en) IN (q)] with [n > 1] *)
  | F_Row_In.

Record dialect : Type :=
  mk_dialect
    {
      (** is this value a NULL? *)
      is_null : value -> bool;
      (** a NULL, used when no type is known *)
      null : value;
      (** the truth value of a value used as a condition *)
      truth_of_value : value -> bool3;
      (** the value of a condition used as an expression *)
      value_of_truth : bool3 -> value;
      (** the equality predicate [=] of SQL, used by IN *)
      eq3 : value -> value -> bool3;
      (** the total order on the values which are not NULL, used by ORDER BY *)
      order : value -> value -> comparison;
      (** integers as values, used by the ranking window functions *)
      value_of_Z : Z -> value;
      (** the number which a value stands for, as the key of a [RANGE] window frame with an offset
          (NULL and the values which are not numbers have none) *)
      rat_of : value -> option Q;
      (** the value which stands for a rational number ([PERCENT_RANK], [CUME_DIST]) *)
      value_of_rat : Q -> value;
      (** The key of a value for the operations which identify values which are
          not distinct without being equal: [GROUP BY], [DISTINCT], the set operations
          and [DISTINCT] aggregates. It is the identity when the comparison of strings is
          deterministic, and for instance the case folding of a string with a case
          insensitive collation. Two NULLs have the same key. *)
      canon : value -> value;
      (** Are NULLs the smallest values of [ORDER BY] (MySQL, SQLite) or the largest ones
          (PostgreSQL, Oracle)? This is only the default: it can be overridden by 
          [NULLS FIRST] and [NULLS LAST] in the dialects which have them. *)
      nulls_smallest : bool;
      (** the constructs which the dialect supports *)
      supports : feature -> bool;
      (** the function symbols, the predicates and the aggregates which the dialect has *)
      known_symbol : symb -> bool;
      known_predicate : predicate -> bool;
      known_aggregate : aggregate -> bool
    }.

Hypothesis O : dialect.

(** * Syntax *)

(** Renaming of the attributes of an item of a FROM clause: either all the
    attributes are kept as they are, or the item is projected on the given
    attributes, each [(a, b)] standing for [a AS b]. *)
Inductive renaming : Type :=
  | Ren_Star
  | Ren_List : list (attribute * attribute) -> renaming.

Inductive sexpr : Type :=
  | E_Const : value -> sexpr
  | E_Col : attribute -> sexpr
  | E_Fun : symb -> list sexpr -> sexpr
  (** [agg ([ALL | DISTINCT] e) FILTER (WHERE c)]; [c] is [C_True] when there is
      no FILTER, and COUNT( * ) is the count of any constant. *)
  | E_Agg : aggregate -> set_quantifier -> sexpr -> scond -> sexpr
  (** [CASE WHEN c THEN e1 ELSE e2 END]: contrarily to a function symbol, only
      one of the branches is evaluated. The general CASE is a cascade of those. *)
  | E_Case : scond -> sexpr -> sexpr -> sexpr
  (** a condition as a boolean value *)
  | E_Cond : scond -> sexpr
  (** scalar subquery *)
  | E_Sub : squery -> sexpr
  (** [GROUPING(e)]: 1 if [e] is not grouped in the current grouping set (its value is NULL there), 0 otherwise *)
  | E_Grouping : sexpr -> sexpr

with scond : Type :=
  | C_Conj : and_or -> scond -> scond -> scond
  | C_Not : scond -> scond
  | C_True : scond
  | C_Pred : predicate -> list sexpr -> scond
  (** a boolean expression as a condition *)
  | C_Expr : sexpr -> scond
  (** [(e1, ..., en) p {ANY | ALL} (q)], the columns [a1, ..., an] of [q] being
      given explicitly: [p] is applied to [e1, ..., en, t.a1, ..., t.an]. *)
  | C_Quant : quantifier -> predicate -> list sexpr -> squery -> list attribute -> scond
  (** [(e1, ..., en) IN (q)], where [a1, ..., an] are the columns of [q] *)
  | C_In : list sexpr -> squery -> list attribute -> scond
  | C_Exists : squery -> scond

with squery : Type :=
  | SQ_Table : relname -> squery
  | SQ_Set : set_op -> set_quantifier -> squery -> squery -> squery
  | SQ_Select : sspec -> squery
  (** [q ORDER BY ... OFFSET ... LIMIT ...] *)
  | SQ_Order : squery -> list sorder -> option N -> option N -> squery
  (** [q ORDER BY ... OFFSET off FETCH FIRST ... ROWS ONLY | WITH TIES]; the boolean tells whether the
      ties of the last row are returned too, the number is a number of rows or a percentage of
      the rows of [q] (computed before the offset, rounded up). *)
  | SQ_Fetch : squery -> list sorder -> option N -> bool -> bool -> N -> squery
  (** [SELECT *, w1, ..., wn FROM q], the [wi] being window functions *)
  | SQ_Window : squery -> list swindow -> squery
  (** [WITH r AS (q1) q2] *)
  | SQ_With : relname -> squery -> squery -> squery
  (** [WITH RECURSIVE r AS (base UNION [ALL] step) body]: [step] reads [r] *)
  | SQ_WithRec : set_quantifier -> relname -> squery -> squery -> squery -> squery

(** A query specification, that is a SELECT block. *)
with sspec : Type :=
  | Select :
      (** all / distinct *) set_quantifier ->
      (** select *) sselect ->
      (** from *) list sfrom ->
      (** where *) scond ->
      (** group by *) sgroup ->
      (** having *) scond -> sspec

with sselect : Type :=
  | S_Star : sselect
  | S_List : list sitem -> sselect

with sitem : Type :=
  | S_As : sexpr -> attribute -> sitem

with sfrom : Type :=
  | Fr_Query : squery -> renaming -> sfrom
  (** [f1 JOIN f2 ON c]; when the boolean is [true], the join is LATERAL: [f2] may
      refer to the attributes of [f1]. *)
  | Fr_Join : join_type -> bool -> sfrom -> sfrom -> scond -> sfrom

with sgroup : Type :=
  (** no GROUP BY. If the SELECT or the HAVING clause contains an aggregate of
      the block, then there is a single group: all the rows. *)
  | G_Fine : sgroup
  (** [GROUP BY e1, ..., en]; when the list is empty, there is a single group. *)
  | G_By : list sexpr -> sgroup
  (** [GROUP BY GROUPING SETS ((e1, e2), (e1), ())]: the rows are grouped for each of the sets *)
  | G_Sets : list (list sexpr) -> sgroup
  (** [GROUP BY ROLLUP (e1, ..., en)]: the sets [(e1, ..., en)], [(e1, ..., en-1)], ..., [()] *)
  | G_Rollup : list sexpr -> sgroup
  (** [GROUP BY CUBE (e1, ..., en)]: all the subsets *)
  | G_Cube : list sexpr -> sgroup

with sorder : Type :=
  | O_By : sexpr -> order_dir -> nulls_order -> sorder

with swindow : Type :=
  (** [w OVER (PARTITION BY e1, ..., en ORDER BY o1, ..., ok) AS a] *)
  | W_As : swfun -> list sexpr -> list sorder -> attribute -> swindow

with swfun : Type :=
  (** an aggregate over the frame of the current row *)
  | W_Agg : aggregate -> set_quantifier -> sexpr -> frame -> swfun
  | W_Row_Number : swfun
  | W_Rank : swfun
  | W_Dense_Rank : swfun
  | W_Ntile : nat -> swfun
  (** [(rank - 1) / (rows - 1)], 0 for a single row *)
  | W_Percent_Rank : swfun
  (** the number of rows which are before the current row or its peers, divided by the number of rows *)
  | W_Cume_Dist : swfun
  (** [LAG (e, n, default)] *)
  | W_Lag : sexpr -> nat -> sexpr -> swfun
  (** [LEAD (e, n, default)] *)
  | W_Lead : sexpr -> nat -> sexpr -> swfun
  | W_First_Value : sexpr -> frame -> swfun
  | W_Last_Value : sexpr -> frame -> swfun
  (** [NTH_VALUE (e, n)], the first row of the frame being the row number 1 *)
  | W_Nth_Value : sexpr -> nat -> frame -> swfun.

(** * Some derived forms *)

(** [e1 AND ... AND en] *)
Definition C_And_N (l : list scond) := fold_right (C_Conj And_F) C_True l.

(** [CASE WHEN c1 THEN e1 ... WHEN cn THEN en ELSE e END] *)
Definition E_Case_N (l : list (scond * sexpr)) (e : sexpr) :=
  fold_right (fun ce acc => E_Case (fst ce) (snd ce) acc) e l.

(** [SELECT e1 AS a1, ..., en AS an], without FROM: a single row. *)
Definition SQ_Row (l : list sitem) :=
  SQ_Select (Select Set_All (S_List l) nil C_True G_Fine C_True).

(** [VALUES (e11, ..., e1n), ..., (ek1, ..., ekn)], the columns of which are
    named [a1, ..., an]. *)
Definition SQ_Values (la : list attribute) (rows : list (list sexpr)) :=
  let row r := SQ_Row (map (fun ea => S_As (fst ea) (snd ea)) (combine r la)) in
  match rows with
  | nil =>
    SQ_Select (Select Set_All (S_List (map (fun a => S_As (E_Col a) a) la)) nil
                      (C_Not C_True) G_Fine C_True)
  | r :: rows => fold_left (fun acc r => SQ_Set Union Set_All acc (row r)) rows (row r)
  end.

(** [f1 CROSS JOIN f2] *)
Definition Fr_Cross f1 f2 := Fr_Join J_Inner false f1 f2 C_True.

(** * Grouping sets *)

Definition rollup_sets {A : Type} (l : list A) : list (list A) :=
  map (fun n => firstn n l) (rev (seq 0 (S (List.length l)))).

Fixpoint cube_sets {A : Type} (l : list A) : list (list A) :=
  match l with
  | nil => nil :: nil
  | x :: r => let sub := cube_sets r in map (cons x) sub ++ sub
  end.

(** The grouping sets of a [GROUP BY] which has some. *)
Definition group_sets (g : sgroup) : option (list (list sexpr)) :=
  match g with
  | G_Sets ss => Some ss
  | G_Rollup l => Some (rollup_sets l)
  | G_Cube l => Some (cube_sets l)
  | _ => None
  end.

(** the expressions of a [GROUP BY] *)
Definition group_exprs (g : sgroup) : list sexpr :=
  match g with
  | G_Fine => nil
  | G_By l | G_Rollup l | G_Cube l => l
  | G_Sets ss => List.concat ss
  end.

(** Equality of the expressions which can be grouping expressions: constants, columns and
    functions of them. *)
Fixpoint sexpr_eqb (e1 e2 : sexpr) {struct e1} : bool :=
  match e1, e2 with
  | E_Const v1, E_Const v2 => Oset.eq_bool (OVal T) v1 v2
  | E_Col a1, E_Col a2 => Oset.eq_bool (OAtt T) a1 a2
  | E_Fun f1 l1, E_Fun f2 l2 => 
    Oset.eq_bool (OSymb T) f1 f2 &&
    (fix eqs (l1 l2 : list sexpr) {struct l1} : bool :=
       match l1, l2 with
       | nil, nil => true
       | x :: r1, y :: r2 => sexpr_eqb x y && eqs r1 r2
       | _, _ => false
       end) l1 l2
  | _, _ => false
  end.

(** * Bare columns

    A column of a block with aggregates which is neither one of the grouping expressions nor
    inside an aggregate has no single value in a group. Subqueries are not inspected, and
    functional dependencies (keys) are not modelled: the check is the syntactic one. *)
Fixpoint bare_e (gs : list sexpr) (e : sexpr) {struct e} : bool :=
  if existsb (sexpr_eqb e) gs then false else
  match e with
  | E_Col _ => true
  | E_Fun _ l => (fix go (l : list sexpr) : bool := match l with nil => false | x :: r => bare_e gs x || go r end) l
  | E_Case c e1 e2 => bare_c gs c || bare_e gs e1 || bare_e gs e2
  | E_Cond c => bare_c gs c
  | _ => false
  end

with bare_c (gs : list sexpr) (c : scond) {struct c} : bool :=
  match c with
  | C_Conj _ c1 c2 => bare_c gs c1 || bare_c gs c2
  | C_Not c => bare_c gs c
  | C_Pred _ l => (fix go (l : list sexpr) : bool := match l with nil => false | x :: r => bare_e gs x || go r end) l
  | C_Expr e => bare_e gs e
  | _ => false
  end.

(** Does the expression contain an aggregate of the block (not inside a subquery)? *)
Fixpoint has_agg_syn (e : sexpr) {struct e} : bool :=
  match e with
  | E_Agg _ _ _ _ => true
  | E_Fun _ l => (fix go (l : list sexpr) : bool := match l with nil => false | x :: r => has_agg_syn x || go r end) l
  | E_Case c e1 e2 => has_agg_c c || has_agg_syn e1 || has_agg_syn e2
  | E_Cond c => has_agg_c c
  | _ => false
  end

with has_agg_c (c : scond) {struct c} : bool :=
  match c with
  | C_Conj _ c1 c2 => has_agg_c c1 || has_agg_c c2
  | C_Not c => has_agg_c c
  | C_Pred _ l => (fix go (l : list sexpr) : bool := match l with nil => false | x :: r => has_agg_syn x || go r end) l
  | C_Expr e => has_agg_syn e
  | _ => false
  end.

Definition block_has_bare_column (s : sselect) (g : sgroup) (h : scond) : bool :=
  let items := match s with S_Star => nil | S_List l => map (fun x => match x with S_As e _ => e end) l end in
  let aggregated := (match g with G_Fine => false | _ => true end) || existsb has_agg_syn items || has_agg_c h in
  aggregated &&
  ((match s with S_Star => true | _ => false end) || 
   existsb (bare_e (group_exprs g)) items || bare_c (group_exprs g) h).

(** * The constructs which a query uses

    [squery_uses q] lists the constructs of [q] which are not supported by all the
    dialects. A dialect accepts [q] if it supports all of them. *)

(** What a query uses, and which a dialect may lack: a construct of the language, a function
    symbol, a predicate or an aggregate. *)
Inductive use : Type :=
  | U_Feature : feature -> use
  | U_Symbol : symb -> use
  | U_Pred : predicate -> use
  | U_Agg : aggregate -> use.


Definition nulls_features (o : sorder) : list use :=
  match o with
  | O_By _ _ Nulls_Default => nil
  | O_By _ _ _ => (U_Feature F_Nulls_Order) :: nil
  end.

Definition frame_bound_is_groups (f : frame) : list use :=
  match f with Frame_Groups _ _ => (U_Feature F_Frame_Groups) :: nil | _ => nil end.

Fixpoint sexpr_uses (e : sexpr) {struct e} : list use :=
  match e with
  | E_Const _ | E_Col _ => nil
  | E_Fun f l => U_Symbol f :: flat_map sexpr_uses l
  | E_Agg ag _ e c => 
    U_Agg ag :: sexpr_uses e ++ scond_uses c ++
    match c with C_True => nil | _ => (U_Feature F_Filter_Agg) :: nil end
  | E_Case c e1 e2 => scond_uses c ++ sexpr_uses e1 ++ sexpr_uses e2
  | E_Cond c => (U_Feature F_Cond_Value) :: scond_uses c
  | E_Sub q => squery_uses q
  | E_Grouping e => sexpr_uses e
  end

with scond_uses (c : scond) {struct c} : list use :=
  match c with
  | C_Conj _ c1 c2 => scond_uses c1 ++ scond_uses c2
  | C_Not c => scond_uses c
  | C_True => nil
  | C_Pred p l => U_Pred p :: flat_map sexpr_uses l
  | C_Expr e => (U_Feature F_Cond_Value) :: sexpr_uses e
  | C_Quant _ p l q _ => (U_Feature F_Any_All) :: U_Pred p :: flat_map sexpr_uses l ++ squery_uses q
  | C_In l q _ => 
    (match l with _ :: _ :: _ => (U_Feature F_Row_In) :: nil | _ => nil end) ++
    flat_map sexpr_uses l ++ squery_uses q
  | C_Exists q => squery_uses q
  end

with squery_uses (q : squery) {struct q} : list use :=
  match q with
  | SQ_Table _ => nil
  | SQ_Set o sq q1 q2 => 
    (match o, sq with
     | Inter, Set_Distinct => (U_Feature F_Intersect) :: nil
     | Inter, Set_All => (U_Feature F_Intersect) :: (U_Feature F_Intersect_All) :: nil
     | Diff, Set_Distinct => (U_Feature F_Except) :: nil
     | Diff, Set_All => (U_Feature F_Except) :: (U_Feature F_Except_All) :: nil
     | _, _ => nil
     end) ++ squery_uses q1 ++ squery_uses q2
  | SQ_Select sp => sspec_uses sp
  | SQ_Order q lo _ _ => 
    squery_uses q ++ flat_map nulls_features lo ++ 
    flat_map (fun o => match o with O_By e _ _ => sexpr_uses e end) lo
  | SQ_Fetch q lo _ ties percent _ => 
    squery_uses q ++ flat_map nulls_features lo ++ 
    flat_map (fun o => match o with O_By e _ _ => sexpr_uses e end) lo ++
    (if ties then (U_Feature F_Fetch_Ties) :: nil else nil) ++
    (if percent then (U_Feature F_Fetch_Percent) :: nil else nil)
  | SQ_Window q lw => 
    (U_Feature F_Window) :: squery_uses q ++
    flat_map (fun w => 
                match w with 
                | W_As f lp lo _ => 
                  flat_map sexpr_uses lp ++ flat_map nulls_features lo ++
                  match f with
                  | W_Agg ag _ e fr => U_Agg ag :: sexpr_uses e ++ frame_bound_is_groups fr
                  | W_First_Value e fr => sexpr_uses e ++ frame_bound_is_groups fr
                  | W_Last_Value e fr => sexpr_uses e ++ frame_bound_is_groups fr
                  | W_Nth_Value e _ fr => sexpr_uses e ++ frame_bound_is_groups fr
                  | W_Lag e _ d => sexpr_uses e ++ sexpr_uses d
                  | W_Lead e _ d => sexpr_uses e ++ sexpr_uses d
                  | _ => nil
                  end
                end) lw
  | SQ_With _ q1 q2 => (U_Feature F_With) :: squery_uses q1 ++ squery_uses q2
  | SQ_WithRec _ _ q1 q2 q3 =>
    (U_Feature F_With) :: (U_Feature F_Recursive) :: squery_uses q1 ++ squery_uses q2 ++ squery_uses q3
  end

with sspec_uses (sp : sspec) {struct sp} : list use :=
  match sp with
  | Select _ s lf w g h =>
    (match s with 
     | S_Star => nil 
     | S_List l => flat_map (fun x => match x with S_As e _ => sexpr_uses e end) l
     end) ++
    flat_map sfrom_uses lf ++ scond_uses w ++
    (match g with 
     | G_Sets _ => (U_Feature F_Grouping_Sets) :: nil 
     | G_Rollup _ => (U_Feature F_Rollup) :: nil 
     | G_Cube _ => (U_Feature F_Cube) :: nil 
     | _ => nil end) ++ (match g with
     | G_Fine => nil
     | G_By l | G_Rollup l | G_Cube l => flat_map sexpr_uses l
     | G_Sets ss => (fix go (ss : list (list sexpr)) : list use := 
                       match ss with nil => nil | l :: r => flat_map sexpr_uses l ++ go r end) ss
     end) ++ 
    scond_uses h ++
    (if block_has_bare_column s g h then (U_Feature F_Bare_Column) :: nil else nil)
  end

with sfrom_uses (f : sfrom) {struct f} : list use :=
  match f with
  | Fr_Query q _ => squery_uses q
  | Fr_Join jt lateral f1 f2 c =>
    (match jt with J_Right => (U_Feature F_Right_Join) :: nil | J_Full => (U_Feature F_Full_Join) :: nil | _ => nil end) ++
    (if lateral then (U_Feature F_Lateral) :: nil else nil) ++
    sfrom_uses f1 ++ sfrom_uses f2 ++ scond_uses c
  end.

Definition use_ok (u : use) : bool :=
  match u with
  | U_Feature f => supports O f
  | U_Symbol f => known_symbol O f
  | U_Pred p => known_predicate O p
  | U_Agg a => known_aggregate O a
  end.

(** The constructs which a query uses. *)
Definition squery_features (q : squery) : list feature :=
  flat_map (fun u => match u with U_Feature f => f :: nil | _ => nil end) (squery_uses q).

(** Does the dialect accept the query? It must support its constructs, and have its functions,
    predicates and aggregates. *)
Definition accepted_by (q : squery) : bool := forallb use_ok (squery_uses q).

(** * Sort of a query: the set of the attributes of its result

    The common table expressions which are in scope are given by an association
    list, together with their (already evaluated) contents. *)

Hypothesis basesort : relname -> setA.
Hypothesis instance : relname -> bagT.

Definition cte_env := list (relname * (setA * list tuple)).

Definition sitem_att (x : sitem) := match x with S_As _ a => a end.
Definition swindow_att (x : swindow) := match x with W_As _ _ _ a => a end.

Fixpoint squery_sort (ce : cte_env) (q : squery) {struct q} : setA :=
  match q with
  | SQ_Table r =>
    match Oset.find ORN r ce with
    | Some (s, _) => s
    | None => basesort r
    end
  | SQ_Set _ _ q1 _ => squery_sort ce q1
  | SQ_Select sp => sspec_sort ce sp
  | SQ_Order q _ _ _ => squery_sort ce q
  | SQ_Fetch q _ _ _ _ _ => squery_sort ce q
  | SQ_Window q lw =>
    Fset.union (A T) (squery_sort ce q) (Fset.mk_set (A T) (map swindow_att lw))
  | SQ_With r q1 q2 => squery_sort ((r, (squery_sort ce q1, nil)) :: ce) q2
  | SQ_WithRec _ r q1 _ q3 => squery_sort ((r, (squery_sort ce q1, nil)) :: ce) q3
  end

with sspec_sort (ce : cte_env) (sp : sspec) {struct sp} : setA :=
  match sp with
  | Select _ S_Star lf _ _ _ => Fset.Union (A T) (map (sfrom_sort ce) lf)
  | Select _ (S_List l) _ _ _ _ => Fset.mk_set (A T) (map sitem_att l)
  end

with sfrom_sort (ce : cte_env) (f : sfrom) {struct f} : setA :=
  match f with
  | Fr_Query q Ren_Star => squery_sort ce q
  | Fr_Query _ (Ren_List l) => Fset.mk_set (A T) (map (@snd _ _) l)
  | Fr_Join _ _ f1 f2 _ => Fset.union (A T) (sfrom_sort ce f1) (sfrom_sort ce f2)
  end.

(** * Environments

    An expression is evaluated in an environment, which is a stack of slices,
    the innermost query block first. A slice is a set of attributes together
    with a group of tuples over these attributes: a single tuple when the
    block is not (yet) grouped, the tuples of the current group otherwise. The
    group is empty for an aggregate query without GROUP BY over an empty
    collection. *)

(** The third component of a slice is the list of the grouping expressions which are not grouped in
    the current grouping set: they are NULL there. *)
Definition slice := (setA * list tuple * list sexpr)%type.
Definition senv := list slice.

Definition slice_t (t : tuple) : slice := (labels T t, t :: nil, nil).

(** The number of iterations of a recursive CTE which are computed (the engines bound it too:
    [cte_max_recursion_depth] is 1000 in MySQL). *)
Definition rec_fuel : nat := 1000.

Definition is_distinct (sq : set_quantifier) : bool := match sq with Set_Distinct => true | Set_All => false end.

Definition slice_gs (sa : setA) (g : list tuple) (hid : list sexpr) : slice :=
  (match g with t :: _ => labels T t | nil => sa end, g, hid).

Definition slice_g (sa : setA) (g : list tuple) : slice := slice_gs sa g nil.

(** Is the expression one of the grouping expressions which the current grouping set does not group? *)
Definition is_hidden (env : senv) (e : sexpr) : bool :=
  match env with
  | (_, _, hid) :: _ => match hid with nil => false | _ => existsb (sexpr_eqb e) hid end
  | _ => false
  end.

Definition null_of (a : attribute) := default_value T (type_of_attribute T a).

(** The NULL tuple over a set of attributes: the padding of outer joins. *)
Definition null_tuple (sa : setA) := mk_tuple T sa null_of.

(** A column refers to the innermost slice which binds it. All the tuples of a
    group agree on the grouping columns, and the first one is used. *)
Fixpoint lookup (env : senv) (a : attribute) : value :=
  match env with
  | nil => null_of a
  | (sa, g, _) :: env' =>
    if a inS? sa
    then match g with t :: _ => dot T t a | nil => null_of a end
    else lookup env' a
  end.

(** The value which is stored for attribute [a]: this only makes sure that a
    NULL has the type of [a]. *)
Definition store (a : attribute) (v : value) := if is_null O v then null_of a else v.

(** * Columns and aggregates *)

(** The columns which an expression reads from the blocks which enclose it: its own
    columns, and the columns which its subqueries read from outside themselves (the
    columns of a subquery which its own FROM clause binds are not counted). *)
Fixpoint sexpr_cols (ce : cte_env) (e : sexpr) {struct e} : list attribute :=
  match e with
  | E_Const _ => nil
  | E_Col a => a :: nil
  | E_Fun _ l => flat_map (sexpr_cols ce) l
  | E_Agg _ _ e c => sexpr_cols ce e ++ scond_cols ce c
  | E_Case c e1 e2 => scond_cols ce c ++ sexpr_cols ce e1 ++ sexpr_cols ce e2
  | E_Cond c => scond_cols ce c
  | E_Sub q => squery_cols ce q
  | E_Grouping e => sexpr_cols ce e
  end

with scond_cols (ce : cte_env) (c : scond) {struct c} : list attribute :=
  match c with
  | C_Conj _ c1 c2 => scond_cols ce c1 ++ scond_cols ce c2
  | C_Not c => scond_cols ce c
  | C_True => nil
  | C_Pred _ l => flat_map (sexpr_cols ce) l
  | C_Expr e => sexpr_cols ce e
  | C_Quant _ _ l q _ => flat_map (sexpr_cols ce) l ++ squery_cols ce q
  | C_In l q _ => flat_map (sexpr_cols ce) l ++ squery_cols ce q
  | C_Exists q => squery_cols ce q
  end

(** the columns which a query reads from outside itself *)
with squery_cols (ce : cte_env) (q : squery) {struct q} : list attribute :=
  match q with
  | SQ_Table _ => nil
  | SQ_Set _ _ q1 q2 => squery_cols ce q1 ++ squery_cols ce q2
  | SQ_Select sp => sspec_cols ce sp
  | SQ_Order q _ _ _ => squery_cols ce q
  | SQ_Fetch q lo _ _ _ _ => squery_cols ce q
  | SQ_Window q _ => squery_cols ce q
  | SQ_With r q1 q2 => 
    squery_cols ce q1 ++ squery_cols ((r, (squery_sort ce q1, nil)) :: ce) q2
  | SQ_WithRec _ r q1 q2 q3 => 
    let ce' := (r, (squery_sort ce q1, nil)) :: ce in
    squery_cols ce q1 ++ squery_cols ce' q2 ++ squery_cols ce' q3
  end

with sspec_cols (ce : cte_env) (sp : sspec) {struct sp} : list attribute :=
  match sp with
  | Select _ s lf w g h =>
    let bound := Fset.Union (A T) (map (sfrom_sort ce) lf) in
    let own := 
        (match s with 
         | S_Star => nil 
         | S_List l => flat_map (fun x => match x with S_As e _ => sexpr_cols ce e end) l 
         end) ++
        scond_cols ce w ++
        (match g with
         | G_Fine => nil
         | G_By l | G_Rollup l | G_Cube l => flat_map (sexpr_cols ce) l
         | G_Sets ss => (fix go (ss : list (list sexpr)) : list attribute := 
                           match ss with nil => nil | l :: r => flat_map (sexpr_cols ce) l ++ go r end) ss
         end) ++
        scond_cols ce h ++ flat_map (sfrom_cols ce) lf in
    filter (fun a => negb (a inS? bound)) own
  end

with sfrom_cols (ce : cte_env) (f : sfrom) {struct f} : list attribute :=
  match f with
  | Fr_Query q _ => squery_cols ce q
  | Fr_Join _ _ f1 f2 c => sfrom_cols ce f1 ++ sfrom_cols ce f2 ++ scond_cols ce c
  end.

(** An aggregate belongs to the innermost block which binds one of the columns
    of its argument, and to the block in which it occurs when its argument has
    no column: [agg_env cols env] is the part of the environment which starts
    with the slice of that block. This is how correlated aggregates such as
    [SELECT ... FROM t GROUP BY a HAVING EXISTS (SELECT ... HAVING sum(t.b) > x)]
    are evaluated on the groups of the outer block. *)
Fixpoint agg_env_rec (cols : list attribute) (env : senv) : senv :=
  match env with
  | nil => nil
  | (sa, g, _) :: env' =>
    if existsb (fun a => a inS? sa) cols then env else agg_env_rec cols env'
  end.

Definition agg_env (cols : list attribute) (env : senv) : senv :=
  match agg_env_rec cols env with
  | nil => env
  | env' => env'
  end.

(** Aggregates which are written in a subquery and belong to an enclosing block: an
    aggregate belongs to the innermost block which binds one of its columns, so that
    [SELECT (SELECT sum(t.a) FROM u) FROM t] aggregates the rows of [t]. [sexpr_foreign ce sa bound e]
    tells whether [e], which is in a subquery whose own FROM clause binds [bound], contains
    an aggregate which reads the block of sort [sa] and nothing of the subquery. *)
Fixpoint sexpr_foreign (ce : cte_env) (sa bound : setA) (e : sexpr) {struct e} : bool :=
  match e with
  | E_Const _ | E_Col _ => false
  | E_Fun _ l => existsb (sexpr_foreign ce sa bound) l
  | E_Agg _ _ a c =>
    match sexpr_cols ce a ++ scond_cols ce c with
    | nil => false
    | cols => existsb (fun x => x inS? sa) cols && negb (existsb (fun x => x inS? bound) cols)
    end
  | E_Case c e1 e2 => 
    scond_foreign ce sa bound c || sexpr_foreign ce sa bound e1 || sexpr_foreign ce sa bound e2
  | E_Cond c => scond_foreign ce sa bound c
  | E_Sub q => squery_foreign ce sa q
  | E_Grouping e => sexpr_foreign ce sa bound e
  end

with scond_foreign (ce : cte_env) (sa bound : setA) (c : scond) {struct c} : bool :=
  match c with
  | C_Conj _ c1 c2 => scond_foreign ce sa bound c1 || scond_foreign ce sa bound c2
  | C_Not c => scond_foreign ce sa bound c
  | C_True => false
  | C_Pred _ l => existsb (sexpr_foreign ce sa bound) l
  | C_Expr e => sexpr_foreign ce sa bound e
  | C_Quant _ _ l q _ => existsb (sexpr_foreign ce sa bound) l || squery_foreign ce sa q
  | C_In l q _ => existsb (sexpr_foreign ce sa bound) l || squery_foreign ce sa q
  | C_Exists q => squery_foreign ce sa q
  end

with squery_foreign (ce : cte_env) (sa : setA) (q : squery) {struct q} : bool :=
  match q with
  | SQ_Table _ => false
  | SQ_Set _ _ q1 q2 => squery_foreign ce sa q1 || squery_foreign ce sa q2
  | SQ_Select (Select _ s lf w _ h) =>
    let bound := Fset.Union (A T) (map (sfrom_sort ce) lf) in
    (match s with
     | S_Star => false
     | S_List l => existsb (fun x => match x with S_As e _ => sexpr_foreign ce sa bound e end) l
     end) || scond_foreign ce sa bound h || scond_foreign ce sa bound w
  | SQ_Order q _ _ _ => squery_foreign ce sa q
  | SQ_Fetch q _ _ _ _ _ => squery_foreign ce sa q
  | SQ_Window q _ => squery_foreign ce sa q
  | SQ_With r q1 q2 => 
    squery_foreign ce sa q1 || squery_foreign ((r, (squery_sort ce q1, nil)) :: ce) sa q2
  | SQ_WithRec _ r q1 q2 q3 => 
    let ce' := (r, (squery_sort ce q1, nil)) :: ce in
    squery_foreign ce sa q1 || squery_foreign ce' sa q2 || squery_foreign ce' sa q3
  end.

(** Does this expression contain an aggregate of the block, the FROM clause of
    which has sort [sa]? The aggregates which the subqueries contain are not counted,
    but their columns are, when they read the block. *)
Fixpoint sexpr_has_agg (ce : cte_env) (sa : setA) (e : sexpr) : bool :=
  match e with
  | E_Const _ | E_Col _ => false
  | E_Sub q => squery_foreign ce sa q
  | E_Grouping _ => false
  | E_Fun _ l => existsb (sexpr_has_agg ce sa) l
  | E_Agg _ _ e c =>
    match sexpr_cols ce e ++ scond_cols ce c with
    | nil => true
    | cols => existsb (fun a => a inS? sa) cols
    end
  | E_Case c e1 e2 => scond_has_agg ce sa c || sexpr_has_agg ce sa e1 || sexpr_has_agg ce sa e2
  | E_Cond c => scond_has_agg ce sa c
  end

with scond_has_agg (ce : cte_env) (sa : setA) (c : scond) : bool :=
  match c with
  | C_Conj _ c1 c2 => scond_has_agg ce sa c1 || scond_has_agg ce sa c2
  | C_Not c => scond_has_agg ce sa c
  | C_True => false
  | C_Exists q => squery_foreign ce sa q
  | C_Pred _ l => existsb (sexpr_has_agg ce sa) l
  | C_Expr e => sexpr_has_agg ce sa e
  | C_Quant _ _ l q _ => existsb (sexpr_has_agg ce sa) l || squery_foreign ce sa q
  | C_In l q _ => existsb (sexpr_has_agg ce sa) l || squery_foreign ce sa q
  end.

Definition sselect_has_agg (ce : cte_env) (sa : setA) (s : sselect) :=
  match s with
  | S_Star => false
  | S_List l => existsb (fun x => match x with S_As e _ => sexpr_has_agg ce sa e end) l
  end.

(** * Collections of tuples as lists

    The result of a query is a list of tuples. Except after an ORDER BY, only
    the underlying bag is meaningful; the order of the list is however always
    determined, which gives a deterministic meaning to the constructs of SQL
    the result of which is implementation dependent, such as LIMIT without a
    total ORDER BY. *)

Section Lists.

Variable X : Type.

(** Tuples are identified through the keys of their values. *)
Definition canon_tuple (t : tuple) : tuple := 
  mk_tuple T (labels T t) (fun a => canon O (dot T t a)).

Definition tuple_mem (t : tuple) (l : list tuple) := 
  Oeset.mem_bool (OTuple T) (canon_tuple t) (map canon_tuple l).

(** Removal of the duplicates, w.r.t. a projection on tuples; the first
    occurrence is kept. *)
Fixpoint dedup_rec (f : X -> tuple) (seen : list tuple) (l : list X) : list X :=
  match l with
  | nil => nil
  | x :: l =>
    if tuple_mem (f x) seen
    then dedup_rec f seen l
    else x :: dedup_rec f (f x :: seen) l
  end.

Definition dedup_on (f : X -> tuple) (l : list X) := dedup_rec f nil l.

(** Groups, in the order of the first occurrence of their keys; inside a group,
    the order of the list is kept. *)
Definition key_eqb (k1 k2 : list value) := 
  Oset.eq_bool (mk_olists (OVal T)) (map (canon O) k1) (map (canon O) k2).

Fixpoint group_insert (k : list value) (x : X) (gs : list (list value * list X)) :=
  match gs with
  | nil => (k, x :: nil) :: nil
  | (k', g) :: gs' =>
    if key_eqb k k' then (k', g ++ x :: nil) :: gs' else (k', g) :: group_insert k x gs'
  end.

Definition group_on (key : X -> list value) (l : list X) : list (list X) :=
  map (@snd _ _) (fold_left (fun gs x => group_insert (key x) x gs) l nil).

(** Stable sort by insertion. *)
Fixpoint insert_sorted (le : X -> X -> bool) (x : X) (l : list X) :=
  match l with
  | nil => x :: nil
  | y :: l' => if le x y then x :: l else y :: insert_sorted le x l'
  end.

Definition stable_sort (le : X -> X -> bool) (l : list X) :=
  fold_right (insert_sorted le) nil l.

Fixpoint indexed_rec (i : nat) (l : list X) : list (nat * X) :=
  match l with
  | nil => nil
  | x :: l => (i, x) :: indexed_rec (S i) l
  end.

Definition indexed := indexed_rec 0.

End Lists.

Definition dedup := dedup_on (fun t : tuple => t).

Fixpoint value_dedup (l : list value) :=
  match l with
  | nil => nil
  | v :: l => v :: filter (fun v' => negb (Oset.eq_bool (OVal T) (canon O v) (canon O v'))) 
                          (value_dedup l)
  end.

Definition quantify (sq : set_quantifier) (l : list value) :=
  match sq with
  | Set_All => l
  | Set_Distinct => value_dedup l
  end.

(** * ORDER BY *)

Definition nulls_first (d : order_dir) (n : nulls_order) :=
  match n with
  | Nulls_First => true
  | Nulls_Last => false
  | Nulls_Default => 
    (* NULLs are the smallest values (they come first in ascending order) or the 
       largest ones, depending on the dialect *)
    match d with Asc => nulls_smallest O | Desc => negb (nulls_smallest O) end
  end.

Definition order_spec := (order_dir * nulls_order)%type.

Definition compare_value (s : order_spec) (v1 v2 : value) : comparison :=
  match s with
  | (d, n) =>
    match is_null O v1, is_null O v2 with
    | true, true => Eq
    | true, false => if nulls_first d n then Lt else Gt
    | false, true => if nulls_first d n then Gt else Lt
    | false, false =>
      match d with
      | Asc => order O v1 v2
      | Desc => CompOpp (order O v1 v2)
      end
    end
  end.

(** Lexicographic comparison of two lists of sort keys. *)
Fixpoint compare_keys (specs : list order_spec) (k1 k2 : list value) : comparison :=
  match specs, k1, k2 with
  | s :: specs, v1 :: k1, v2 :: k2 =>
    match compare_value s v1 v2 with
    | Eq => compare_keys specs k1 k2
    | c => c
    end
  | _, _, _ => Eq
  end.

Definition keys_le specs (k1 k2 : list value) :=
  match compare_keys specs k1 k2 with Gt => false | _ => true end.

Definition sort_on (X : Type) (specs : list order_spec) (keys : X -> list value) (l : list X) :=
  map (@snd _ _)
      (stable_sort (fun x y => keys_le specs (fst x) (fst y)) (map (fun x => (keys x, x)) l)).

Definition sorder_spec (o : sorder) : order_spec := match o with O_By _ d n => (d, n) end.

Definition offset_limit (X : Type) (off lim : option N) (l : list X) :=
  let l' := match off with Some n => skipn (N.to_nat n) l | None => l end in
  match lim with Some n => firstn (N.to_nat n) l' | None => l' end.

(** * Window functions

    The evaluation of window functions does not depend on the syntax of
    expressions: they are first compiled into functions over tuples. *)

Inductive wsem : Type :=
  | WS_Agg : aggregate -> set_quantifier -> (tuple -> value) -> frame -> wsem
  | WS_Row_Number : wsem
  | WS_Rank : wsem
  | WS_Dense_Rank : wsem
  | WS_Ntile : nat -> wsem
  | WS_Percent_Rank : wsem
  | WS_Cume_Dist : wsem
  (** [true] for LAG, [false] for LEAD *)
  | WS_Shift : bool -> (tuple -> value) -> nat -> (tuple -> value) -> wsem
  | WS_First : (tuple -> value) -> frame -> wsem
  | WS_Last : (tuple -> value) -> frame -> wsem
  | WS_Nth : (tuple -> value) -> nat -> frame -> wsem.

(** The number of the group of peers of each row of a sorted partition. *)
Fixpoint peer_groups specs (prev : option (list value)) (cur : nat) (ks : list (list value)) :=
  match ks with
  | nil => nil
  | k :: ks' =>
    let cur' := match prev with
                | None => 0
                | Some p => match compare_keys specs p k with Eq => cur | _ => S cur end
                end in
    cur' :: peer_groups specs (Some k) cur' ks'
  end.

(** Is position [pj] in the frame of position [pi]? *)
Definition after_start (b : frame_bound) (pi pj : nat) :=
  match b with
  | Unbounded_Preceding => true
  | Preceding k => Nat.leb pi (pj + k)
  | Current_Row => Nat.leb pi pj
  | Following k => Nat.leb (pi + k) pj
  | Unbounded_Following => false
  end.

Definition before_end (b : frame_bound) (pi pj : nat) :=
  match b with
  | Unbounded_Preceding => false
  | Preceding k => Nat.leb (pj + k) pi
  | Current_Row => Nat.leb pj pi
  | Following k => Nat.leb pj (pi + k)
  | Unbounded_Following => true
  end.

(** The positions of a [RANGE] frame with offsets. [rk] are the keys of the rows (negated for a
    descending order, so that they ascend), [gidx] the numbers of the groups of peers. *)
Definition range_after_start (b : frame_bound) (rk : list (option Q)) (gidx : list nat) (pi pj : nat) :=
  let ki := nth pi rk None in
  let kj := nth pj rk None in
  match b with
  | Unbounded_Preceding => true
  | Current_Row => Nat.leb (nth pi gidx 0) (nth pj gidx 0)
  | Preceding k => match ki, kj with
                   | Some a, Some b => Qle_bool (Qminus a (inject_Z (Z.of_nat k))) b
                   | None, None => true
                   | _, _ => false
                   end
  | Following k => match ki, kj with
                   | Some a, Some b => Qle_bool (Qplus a (inject_Z (Z.of_nat k))) b
                   | None, None => true
                   | _, _ => false
                   end
  | Unbounded_Following => false
  end.

Definition range_before_end (b : frame_bound) (rk : list (option Q)) (gidx : list nat) (pi pj : nat) :=
  let ki := nth pi rk None in
  let kj := nth pj rk None in
  match b with
  | Unbounded_Preceding => false
  | Current_Row => Nat.leb (nth pj gidx 0) (nth pi gidx 0)
  | Preceding k => match ki, kj with
                   | Some a, Some b => Qle_bool b (Qminus a (inject_Z (Z.of_nat k)))
                   | None, None => true
                   | _, _ => false
                   end
  | Following k => match ki, kj with
                   | Some a, Some b => Qle_bool b (Qplus a (inject_Z (Z.of_nat k)))
                   | None, None => true
                   | _, _ => false
                   end
  | Unbounded_Following => true
  end.

(** The rows of the frame of the row number [i] of a sorted partition, [gidx]
    being the numbers of the groups of peers of its rows. *)
Definition frame_rows (fr : frame) (sorted : list tuple) (gidx : list nat) (rk : list (option Q)) (i : nat) :=
  match fr with
  | Frame_Range lo hi =>
    map (@snd _ _)
        (filter (fun x => range_after_start lo rk gidx i (fst x) && range_before_end hi rk gidx i (fst x))
                (combine (seq 0 (List.length sorted)) sorted))
  | _ =>
  let (pos, lohi) :=
      match fr with
      | Frame_Rows lo hi => (seq 0 (List.length sorted), (lo, hi))
      | Frame_Groups lo hi | Frame_Range lo hi => (gidx, (lo, hi))
      end in
  let pi := nth i pos 0 in
  map (@snd _ _)
      (filter (fun x => after_start (fst lohi) pi (fst x) && before_end (snd lohi) pi (fst x))
              (combine pos sorted))
  end.

Definition ntile (buckets n i : nat) : Z :=
  let q := Nat.div n buckets in
  let r := Nat.modulo n buckets in
  Z.of_nat (if Nat.ltb i (r * S q)
            then S (Nat.div i (S q))
            else S (r + Nat.div (i - r * S q) q)).

(** The value of a window function for the row [t], which is the row number [i]
    (starting from 0) of its sorted partition. *)
Definition eval_wsem (a : attribute) (w : wsem)
           (sorted : list tuple) (gidx : list nat) (rk : list (option Q)) (i : nat) (t : tuple) : value :=
  match w with
  | WS_Agg ag sq arg fr =>
    interp_aggregate T ag (quantify sq (map arg (frame_rows fr sorted gidx rk i)))
  | WS_Row_Number => value_of_Z O (Z.of_nat (S i))
  | WS_Rank =>
    let gi := nth i gidx 0 in
    value_of_Z O (Z.of_nat (S (List.length (filter (fun g => Nat.ltb g gi) gidx))))
  | WS_Dense_Rank => value_of_Z O (Z.of_nat (S (nth i gidx 0)))
  | WS_Percent_Rank =>
    let gi := nth i gidx 0 in
    let n := List.length sorted in
    let r := List.length (filter (fun g => Nat.ltb g gi) gidx) in
    value_of_rat O (match n with
                    | S (S _) => Qdiv (inject_Z (Z.of_nat r)) (inject_Z (Z.of_nat (Nat.pred n)))
                    | _ => 0%Z # 1
                    end)
  | WS_Cume_Dist =>
    let gi := nth i gidx 0 in
    let n := List.length sorted in
    let k := List.length (filter (fun g => Nat.leb g gi) gidx) in
    value_of_rat O (Qdiv (inject_Z (Z.of_nat k)) (inject_Z (Z.of_nat n)))
  | WS_Ntile b =>
    match b with
    | 0 => null_of a
    | _ => value_of_Z O (ntile b (List.length sorted) i)
    end
  | WS_Shift back arg k dflt =>
    let j := if back then (if Nat.leb k i then Some (i - k) else None) else Some (i + k) in
    match j with
    | Some j => match nth_error sorted j with Some t' => arg t' | None => dflt t end
    | None => dflt t
    end
  | WS_First arg fr =>
    match frame_rows fr sorted gidx rk i with t' :: _ => arg t' | nil => null_of a end
  | WS_Last arg fr =>
    match rev (frame_rows fr sorted gidx rk i) with t' :: _ => arg t' | nil => null_of a end
  | WS_Nth arg n fr =>
    match n with
    | 0 => null_of a
    | S n => match nth_error (frame_rows fr sorted gidx rk i) n with
             | Some t' => arg t'
             | None => null_of a
             end
    end
  end.

(** [t] extended with the value [v] for the attribute [a]. *)
Definition extend_tuple (t : tuple) (a : attribute) (v : value) :=
  mk_tuple T (Fset.union (A T) (labels T t) (Fset.singleton (A T) a))
           (fun x => if Oset.eq_bool (OAtt T) x a then store a v else dot T t x).

(** A window function is evaluated partition by partition, each partition being
    sorted; every row is extended with a new attribute. *)
Definition eval_window
           (part : tuple -> list value) (specs : list order_spec) (keys : tuple -> list value)
           (a : attribute) (w : wsem) (rows : list tuple) : list tuple :=
  flat_map
    (fun g =>
       let sorted := sort_on specs keys g in
       let gidx := peer_groups specs None 0 (map keys sorted) in
       let rk := map (fun k => match k with
                               | v :: _ => match rat_of O v with
                                           | Some q => Some (match specs with (Desc, _) :: _ => Qopp q | _ => q end)
                                           | None => None
                                           end
                               | nil => None
                               end) (map keys sorted) in
       map (fun it => extend_tuple (snd it) a (eval_wsem a w sorted gidx rk (fst it) (snd it)))
           (indexed sorted))
    (group_on part rows).

(** * Joins *)

Definition cross_product (l1 l2 : list tuple) :=
  flat_map (fun t1 => map (join_tuple T t1) l2) l1.

(** [s1] and [s2] are the sorts of the two sides, [l1] the tuples of the left
    hand side, [right t1] the tuples of the right hand side which are to be
    combined with [t1] (this depends on [t1] for a lateral join only), [l2] the
    tuples of the right hand side for the padding of a right or of a full join,
    and [on t] tells whether the combined tuple [t] satisfies the condition of
    the join. *)
Definition eval_join (jt : join_type) (s1 s2 : setA)
           (l1 : list tuple) (right : tuple -> list tuple) (l2 : list tuple)
           (on : tuple -> bool) : list tuple :=
  let matches t1 := filter on (map (join_tuple T t1) (right t1)) in
  let inner := flat_map matches l1 in
  let left_outer :=
      flat_map (fun t1 => match matches t1 with
                          | nil => join_tuple T t1 (null_tuple s2) :: nil
                          | l => l
                          end) l1 in
  let right_padding :=
      map (fun t2 => join_tuple T (null_tuple s1) t2)
          (filter (fun t2 => negb (existsb (fun t1 => on (join_tuple T t1 t2)) l1)) l2) in
  match jt with
  | J_Inner => inner
  | J_Left => left_outer
  | J_Right => inner ++ right_padding
  | J_Full => left_outer ++ right_padding
  end.

Definition rename_tuple (rho : renaming) (t : tuple) :=
  match rho with
  | Ren_Star => t
  | Ren_List l =>
    mk_tuple T (Fset.mk_set (A T) (map (@snd _ _) l))
             (fun b => match Oset.find (OAtt T) b (map (fun x => (snd x, fst x)) l) with
                       | Some a => store b (dot T t a)
                       | None => null_of b
                       end)
  end.

(** * Set operations *)

(** Number of tuples of [l] which are not distinct from [t]. *)
Definition tuple_count (t : tuple) (l : list tuple) :=
  List.length (filter (fun u => Oeset.eq_bool (OTuple T) (canon_tuple t) (canon_tuple u)) l).

(** The elements of [l] which are the [i]-th occurrence of their key, for some [i]
    such that [keep i t] holds: the multiplicity of a tuple in the result is determined
    by [keep]. *)
Fixpoint filter_occ (keep : nat -> tuple -> bool) (before : list tuple) (l : list tuple) :=
  match l with
  | nil => nil
  | t :: l => 
    (if keep (tuple_count t before) t then t :: nil else nil) ++ filter_occ keep (t :: before) l
  end.

Definition eval_set_op (o : set_op) (sq : set_quantifier) (l1 l2 : list tuple) :=
  match sq, o with
  | Set_All, Union => l1 ++ l2
  (** the multiplicity of [t] in [INTERSECT ALL] is the minimum of the multiplicities *)
  | Set_All, Inter => filter_occ (fun i t => Nat.ltb i (tuple_count t l2)) nil l1
  (** and in [EXCEPT ALL] it is their difference, down to 0 *)
  | Set_All, Diff => filter_occ (fun i t => Nat.leb (tuple_count t l2) i) nil l1
  | Set_All, UnionMax =>
    l1 ++ filter_occ (fun i t => Nat.leb (tuple_count t l1) i) nil l2
  | Set_Distinct, Union | Set_Distinct, UnionMax => dedup (l1 ++ l2)
  | Set_Distinct, Inter => filter (fun t => tuple_mem t l2) (dedup l1)
  | Set_Distinct, Diff => filter (fun t => negb (tuple_mem t l2)) (dedup l1)
  end.

(** * Evaluation *)

Definition is_true3 (b : bool3) := Bool.is_true (B T) b.

Fixpoint row_eq3 (l1 l2 : list value) : bool3 :=
  match l1, l2 with
  | v1 :: l1, v2 :: l2 => Bool.andb (B T) (eq3 O v1 v2) (row_eq3 l1 l2)
  | _, _ => Bool.true (B T)
  end.

(** The tuple which is built by a SELECT, from the values of its items. *)
Definition mk_row (l : list (attribute * value)) :=
  mk_tuple T (Fset.mk_set (A T) (map (@fst _ _) l))
           (fun a => match Oset.find (OAtt T) a l with
                     | Some v => store a v
                     | None => null_of a
                     end).

(** Without GROUP BY, is the block nevertheless an aggregate query, with a
    single group? *)
Definition implicit_group (ce : cte_env) (sa : setA) (s : sselect) (h : scond) (ex : list sexpr) :=
  sselect_has_agg ce sa s || scond_has_agg ce sa h || existsb (sexpr_has_agg ce sa) ex.

(** The sort key of a row: a column of the row itself when the key is the name
    of such a column, the key evaluated in the environment of the row
    otherwise (for a SELECT, this gives access to the columns of the FROM clause
    and to the aggregates). *)
Definition is_output_col (t : tuple) (e : sexpr) :=
  match e with
  | E_Col a => if a inS? labels T t then Some (dot T t a) else None
  | _ => None
  end.

Fixpoint eval_sexpr (ce : cte_env) (env : senv) (e : sexpr) {struct e} : value :=
  if is_hidden env e
  then null O
  else 
  match e with
  | E_Grouping x => 
    value_of_Z O (match env with
                  | (_, _, hid) :: _ => if existsb (sexpr_eqb x) hid then 1%Z else 0%Z
                  | nil => 0%Z
                  end)
  | E_Const v => v
  | E_Col a => lookup env a
  | E_Fun f l => interp_symbol T f (map (eval_sexpr ce env) l)
  | E_Agg ag sq e c =>
    let vals :=
        match agg_env (sexpr_cols ce e ++ scond_cols ce c) env with
        | nil => nil
        | (sa, g, _) :: env' =>
          map (fun t => eval_sexpr ce ((sa, t :: nil, nil) :: env') e)
              (filter (fun t => is_true3 (eval_scond ce ((sa, t :: nil, nil) :: env') c)) g)
        end in
    interp_aggregate T ag (quantify sq vals)
  | E_Case c e1 e2 =>
    if is_true3 (eval_scond ce env c) then eval_sexpr ce env e1 else eval_sexpr ce env e2
  | E_Cond c => value_of_truth O (eval_scond ce env c)
  | E_Sub q =>
    match eval_squery ce env q with
    | t :: nil => match {{{labels T t}}} with a :: nil => dot T t a | _ => null O end
    | _ => null O
    end
  end

with eval_scond (ce : cte_env) (env : senv) (c : scond) {struct c} : bool3 :=
  match c with
  | C_Conj a c1 c2 => interp_conj (B T) a (eval_scond ce env c1) (eval_scond ce env c2)
  | C_Not c => Bool.negb (B T) (eval_scond ce env c)
  | C_True => Bool.true (B T)
  | C_Pred p l => interp_predicate T p (map (eval_sexpr ce env) l)
  | C_Expr e => truth_of_value O (eval_sexpr ce env e)
  | C_Quant qtf p l q la =>
    let lv := map (eval_sexpr ce env) l in
    interp_quant (B T) qtf
                 (fun t => interp_predicate T p (lv ++ map (dot T t) la))
                 (eval_squery ce env q)
  | C_In l q la =>
    let lv := map (eval_sexpr ce env) l in
    interp_quant (B T) Exists_F
                 (fun t => row_eq3 lv (map (dot T t) la))
                 (eval_squery ce env q)
  | C_Exists q =>
    match eval_squery ce env q with
    | nil => Bool.false (B T)
    | _ => Bool.true (B T)
    end
  end

with eval_squery (ce : cte_env) (env : senv) (q : squery) {struct q} : list tuple :=
  match q with
  | SQ_Table r =>
    match Oset.find ORN r ce with
    | Some (_, l) => l
    | None => Febag.elements BTupleT (instance r)
    end
  | SQ_Set o sq q1 q2 =>
    if Fset.equal (A T) (squery_sort ce q1) (squery_sort ce q2)
    then eval_set_op o sq (eval_squery ce env q1) (eval_squery ce env q2)
    else nil
  | SQ_Select sp => map (@fst _ _) (eval_sspec ce env sp nil)
  | SQ_Order q lo off lim =>
    let rows :=
        match q with
        | SQ_Select sp => eval_sspec ce env sp (map (fun o => match o with O_By e _ _ => e end) lo)
        | _ => map (fun t => (t, slice_t t :: env)) (eval_squery ce env q)
        end in
    let keys (x : tuple * senv) :=
        map (fun o => match o with
                      | O_By e _ _ =>
                        match is_output_col (fst x) e with
                        | Some v => v
                        | None => eval_sexpr ce (snd x) e
                        end
                      end) lo in
    map (@fst _ _) (offset_limit off lim (sort_on (map sorder_spec lo) keys rows))
  | SQ_Fetch q lo off ties percent n =>
    let rows :=
        match q with
        | SQ_Select sp => eval_sspec ce env sp (map (fun o => match o with O_By e _ _ => e end) lo)
        | _ => map (fun t => (t, slice_t t :: env)) (eval_squery ce env q)
        end in
    let keys (x : tuple * senv) :=
        map (fun o => match o with
                      | O_By e _ _ =>
                        match is_output_col (fst x) e with
                        | Some v => v
                        | None => eval_sexpr ce (snd x) e
                        end
                      end) lo in
    let specs := map sorder_spec lo in
    let sorted := sort_on specs keys rows in
    let after := match off with Some k => skipn (N.to_nat k) sorted | None => sorted end in
    let count := if percent
                 then Nat.div (N.to_nat n * List.length sorted + 99) 100
                 else N.to_nat n in
    let first := firstn count after in
    let rest := skipn count after in
    let extra :=
        if ties
        then match rev first with
             | last :: _ =>
               (fix take (l : list (tuple * senv)) : list (tuple * senv) :=
                  match l with
                  | x :: l' => match compare_keys specs (keys last) (keys x) with
                               | Eq => x :: take l'
                               | _ => nil
                               end
                  | nil => nil
                  end) rest
             | nil => nil
             end
        else nil in
    map (@fst _ _) (first ++ extra)
  | SQ_Window q lw =>
    let compiled :=
        map (fun w =>
               match w with
               | W_As f lp lo a =>
                 let ev e (t : tuple) := eval_sexpr ce (slice_t t :: env) e in
                 let part t := map (fun e => ev e t) lp in
                 let keys t := map (fun o => match o with O_By e _ _ => ev e t end) lo in
                 let f' :=
                     match f with
                     | W_Agg ag sq e fr => WS_Agg ag sq (ev e) fr
                     | W_Row_Number => WS_Row_Number
                     | W_Rank => WS_Rank
                     | W_Dense_Rank => WS_Dense_Rank
                     | W_Ntile n => WS_Ntile n
                     | W_Percent_Rank => WS_Percent_Rank
                     | W_Cume_Dist => WS_Cume_Dist
                     | W_Lag e n d => WS_Shift true (ev e) n (ev d)
                     | W_Lead e n d => WS_Shift false (ev e) n (ev d)
                     | W_First_Value e fr => WS_First (ev e) fr
                     | W_Last_Value e fr => WS_Last (ev e) fr
                     | W_Nth_Value e n fr => WS_Nth (ev e) n fr
                     end in
                 eval_window part (map sorder_spec lo) keys a f'
               end) lw in
    fold_left (fun rows w => w rows) compiled (eval_squery ce env q)
  | SQ_With r q1 q2 =>
    eval_squery ((r, (squery_sort ce q1, eval_squery ce env q1)) :: ce) env q2
  | SQ_WithRec sq r q1 q2 q3 =>
    let sa := squery_sort ce q1 in
    let dedup (l : list tuple) := eval_set_op Union Set_Distinct l nil in
    let base := if is_distinct sq then dedup (eval_squery ce env q1) else eval_squery ce env q1 in
    (* the working table is replaced at each step; [rec_fuel] bounds the number of steps *)
    let res :=
        (fix loop (n : nat) (acc work : list tuple) {struct n} : list tuple :=
           match n with
           | S n' =>
             match work with
             | nil => acc
             | _ =>
               let new := eval_squery ((r, (sa, work)) :: ce) env q2 in
               let new' := if is_distinct sq then eval_set_op Diff Set_Distinct new acc else new in
               loop n' (acc ++ new') new'
             end
           | _ => acc
           end) rec_fuel base base in
    eval_squery ((r, (sa, res)) :: ce) env q3
  end

(** The rows of a SELECT block, each of them together with the environment in
    which it has been built, that is the environment of its group. *)
with eval_sspec (ce : cte_env) (env : senv) (sp : sspec) (ex : list sexpr) {struct sp}
     : list (tuple * senv) :=
  match sp with
  | Select sq s lf w g h =>
    (** the sort of the FROM clause *)
    let sa := Fset.Union (A T) (map (sfrom_sort ce) lf) in
    (** FROM: the product of the items *)
    let from :=
        fold_left cross_product (map (eval_sfrom ce env) lf) (empty_tuple T :: nil) in
    (** WHERE *)
    let rows := filter (fun t => is_true3 (eval_scond ce (slice_t t :: env) w)) from in
    (** GROUP BY *)
    let plain_groups :=
        match g with
        | G_Fine => if implicit_group ce sa s h ex then rows :: nil else map (fun t => t :: nil) rows
        | G_By nil => rows :: nil
        | G_By lg => group_on (fun t => map (eval_sexpr ce (slice_t t :: env)) lg) rows
        | _ => nil
        end in
    (** With grouping sets, the grouping expressions are evaluated once for each row; each grouping set is a
        list of positions in the list [univ] of all the grouping expressions. The groups of a set are
        those of the rows which agree on its expressions, and the expressions of [univ] which it does not
        contain are NULL in the groups it produces. *)
    let univ : list sexpr := 
        match g with
        | G_Sets ss => List.concat ss
        | G_Rollup l | G_Cube l => l
        | _ => nil
        end in
    let row_vals (t : tuple) : list value :=
        match g with
        | G_Sets ss => 
          (fix go (ss : list (list sexpr)) : list value :=
             match ss with
             | nil => nil
             | l :: r => map (eval_sexpr ce (slice_t t :: env)) l ++ go r
             end) ss
        | G_Rollup l | G_Cube l => map (eval_sexpr ce (slice_t t :: env)) l
        | _ => nil
        end in
    let positions : list (list nat) :=
        match g with
        | G_Sets ss => 
          (fix go (off : nat) (ss : list (list sexpr)) : list (list nat) :=
             match ss with
             | nil => nil
             | l :: r => seq off (List.length l) :: go (off + List.length l)%nat r
             end) 0%nat ss
        | G_Rollup l => rollup_sets (seq 0 (List.length l))
        | G_Cube l => cube_sets (seq 0 (List.length l))
        | _ => nil
        end in
    let groupings : list (list tuple * list sexpr) :=
        match g with
        | G_Sets _ | G_Rollup _ | G_Cube _ =>
          flat_map 
            (fun pos =>
               let set := map (fun i => nth i univ (E_Const (null O))) pos in
               let hid := filter (fun e => negb (existsb (sexpr_eqb e) set)) univ in
               let gs := match pos with
                         | nil => rows :: nil
                         | _ => group_on (fun t => let vs := row_vals t in 
                                                   map (fun i => nth i vs (null O)) pos) rows
                         end in
               map (fun grp => (grp, hid)) gs) positions
        | _ => map (fun grp => (grp, nil)) plain_groups
        end in
    let genvs := map (fun gh => slice_gs sa (fst gh) (snd gh) :: env) groupings in
    (** HAVING *)
    let genvs := filter (fun ge => is_true3 (eval_scond ce ge h)) genvs in
    (** SELECT *)
    let out :=
        map (fun ge =>
               (match s with
                | S_Star =>
                  match ge with
                  | (_, t :: _, _) :: _ => t
                  | _ => null_tuple sa
                  end
                | S_List l =>
                  mk_row (map (fun x => match x with
                                        | S_As e a => (a, eval_sexpr ce ge e)
                                        end) l)
                end, ge)) genvs in
    (** DISTINCT *)
    match sq with
    | Set_All => out
    | Set_Distinct => dedup_on (@fst _ _) out
    end
  end

with eval_sfrom (ce : cte_env) (env : senv) (f : sfrom) {struct f} : list tuple :=
  match f with
  | Fr_Query q rho => map (rename_tuple rho) (eval_squery ce env q)
  | Fr_Join jt lateral f1 f2 c =>
    let l1 := eval_sfrom ce env f1 in
    let l2 := eval_sfrom ce env f2 in
    let right t1 := if lateral then eval_sfrom ce (slice_t t1 :: env) f2 else l2 in
    eval_join jt (sfrom_sort ce f1) (sfrom_sort ce f2) l1 right l2
              (fun t => is_true3 (eval_scond ce (slice_t t :: env) c))
  end.

(** * The semantics of a query

    As a list for the queries the result of which is ordered, and as a bag for
    the other ones. *)

Definition eval_query_list (q : squery) : list tuple := eval_squery nil nil q.

Definition eval_query_bag (q : squery) : bagT := Febag.mk_bag BTupleT (eval_query_list q).

Definition sort_of_query (q : squery) : setA := squery_sort nil q.

End Sec.
