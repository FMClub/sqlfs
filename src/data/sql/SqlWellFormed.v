(** * Well-formedness of queries (TODO 6.2, issue I5)

    [wf_query ce q] is a static check of a query of [SqlFull.v]:
    - scoping: every column the query reads is bound by one of its FROM clauses ([squery_cols] is empty:
      a correlated subquery reads its enclosing blocks, which bind its free columns);
    - no aggregate of a block in its WHERE clause (an error in every dialect: "aggregate functions are not
      allowed in WHERE", MySQL error 1111);
    - the operands of a set operation have the same sort (the arity of [UNION], [INTERSECT], [EXCEPT]).
    The check covers the queries of the FROM clauses and of the WITH clauses; the subqueries in expressions
    are covered by the scoping condition only. [accepted_wf d q] is acceptance by a dialect plus this check. *)
Require Import List Bool String.
Require Import BasicFacts ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection
        FlatData Bool3 Formula SqlFull.

Section Sec.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.
Hypothesis ORN : Oset.Rcd relname.
Hypothesis basesort : relname -> Fset.set (Tuple.A T).

Import Tuple.

Notation squery := (squery T relname).
Notation sfrom := (sfrom T relname).

Fixpoint wf_squery (ce : cte_env T relname) (q : squery) {struct q} : bool :=
  match q with
  | SQ_Table _ _ => true
  | SQ_Set _ _ q1 q2 =>
    Fset.equal (A T) (squery_sort ORN basesort ce q1) (squery_sort ORN basesort ce q2)
    && wf_squery ce q1 && wf_squery ce q2
  | SQ_Select (Select _ _ lf w _ _) =>
    let bound := Fset.Union (A T) (map (sfrom_sort ORN basesort ce) lf) in
    negb (scond_has_agg ORN basesort ce bound w) && forallb (wf_sfrom ce) lf
  | SQ_Order q _ _ _ => wf_squery ce q
  | SQ_Fetch q _ _ _ _ _ => wf_squery ce q
  | SQ_Window q _ => wf_squery ce q
  | SQ_With r q1 q2 =>
    wf_squery ce q1 && wf_squery ((r, (squery_sort ORN basesort ce q1, nil)) :: ce) q2
  | SQ_WithRec _ r q1 q2 q3 =>
    let ce' := (r, (squery_sort ORN basesort ce q1, nil)) :: ce in
    wf_squery ce q1 && wf_squery ce' q2 && wf_squery ce' q3
  end

with wf_sfrom (ce : cte_env T relname) (f : sfrom) {struct f} : bool :=
  match f with
  | Fr_Query q _ => wf_squery ce q
  | Fr_Join _ _ f1 f2 _ => wf_sfrom ce f1 && wf_sfrom ce f2
  | Fr_Fun _ _ _ _ => true
  end.

(** a query is well formed when it is closed (no free column) and passes the checks above *)
Definition wf_query (ce : cte_env T relname) (q : squery) : bool :=
  match squery_cols ORN basesort ce q with nil => wf_squery ce q | _ => false end.

(** acceptance by a dialect and well-formedness *)
Definition accepted_wf (d : dialect T) (ce : cte_env T relname) (q : squery) : bool :=
  accepted_by d q && wf_query ce q.

Lemma accepted_wf_accepted : forall d ce q, accepted_wf d ce q = true -> accepted_by d q = true.
Proof. intros d ce q H; apply andb_true_iff in H; tauto. Qed.

Lemma wf_query_closed : forall ce q, wf_query ce q = true -> squery_cols ORN basesort ce q = nil.
Proof. intros ce q; unfold wf_query; destruct (squery_cols ORN basesort ce q); [reflexivity | discriminate]. Qed.

End Sec.
