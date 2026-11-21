(** * The algebra equivalence on the new semantics (TODO 6.1)

    For a query of the common fragment ([to_full2 q = Some q']), the SqlFull evaluation of its translation
    is bag-equal to the evaluation of its translation into the relational algebra
    ([SqlAlgebra.sql_query_to_alg]): this composes [sql_full_agree2] of [SqlRelateSelect.v] with
    [sql_query_to_alg_is_sound] of [SqlAlgebra.v]. *)
Require Import List.
Require Import BasicFacts OrderedSet FiniteSet FiniteBag FiniteCollection FlatData Sql SqlAlgebra SqlFull
  SqlRelateSelect.
Import Tuple.

Theorem sql_full_alg :
  forall (T : Tuple.Rcd) (relname : Type) (ORN : Oset.Rcd relname) (O : dialect T)
         (basesort : relname -> Fset.set (A T)) (instance : relname -> Febag.bag (Fecol.CBag (CTuple T))),
  (forall v, is_error O v = false) ->
  (forall p l, pred_error O p l = false) ->
  (forall p ks l, cmp_coerce O p ks l = l) ->
  (forall p l, interp_pred O p l = interp_predicate T p l) ->
  (forall f l, interp_fun O f l = interp_symbol T f l) ->
  (forall v, const_of O v = v) ->
  (forall a v, is_null O v = true -> null_of T a = v) ->
  (forall t a, Fset.mem (A T) a (labels T t) = false -> dot T t a = default_value T (type_of_attribute T a)) ->
  (forall t u, Oeset.eq_bool (OTuple T) (canon_tuple O t) (canon_tuple O u) = Oeset.eq_bool (OTuple T) t u) ->
  (forall atts rows, unify_rows O atts rows = rows) ->
  forall unknown (cn : tuple T -> bool), (forall t1 t2, t1 =t= t2 -> cn t1 = cn t2) ->
  well_sorted_sql_table T basesort instance ->
  forall (q : sql_query T relname) (q' : squery T relname),
    to_full2 T relname q = Some q' -> well_sorted2 T relname basesort q = true ->
    weak_well_formed_q basesort q = true ->
    Febag.mk_bag (Fecol.CBag (CTuple T)) (eval_squery ORN O basesort instance nil nil q') =BE=
    eval_query basesort instance unknown cn nil (sql_query_to_alg basesort q).
Proof.
intros T relname ORN O basesort instance H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 unknown cn Hcn W q q' Hq Hs Hw.
apply Febag.equal_trans with (eval_sql_query basesort instance unknown cn nil q).
- apply (sql_full_agree2 T relname ORN O basesort instance H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 unknown cn q q' Hq Hs).
- apply Febag.equal_sym; exact (@sql_query_to_alg_is_sound T relname basesort instance unknown cn Hcn W nil q Hw).
Qed.
