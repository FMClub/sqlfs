(** * The evaluation does not depend on the names of the columns (TODO 8.5)

    An instance of [eval_rename_names] ([Renaming.v]): the table [t (a, b)] and the table [t (x, b)] with the
    same rows, and the exchange of the names [a] and [x]. The hypotheses of the theorem hold (by computation for
    the database), and the two evaluations are also compared by computation. *)
Require Import List String ZArith.
Require Import Bool3 FlatData ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull SqlRename.
Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax Dialects MySQL PostgreSQL SpecRunner Renaming.
Import Tuple.
Import ListNotations.
Open Scope string_scope.

Ltac check := vm_compute; reflexivity.

Notation a := (Attr_Z "a").
Notation b := (Attr_Z "b").
Notation x := (Attr_Z "x").
Notation c0 := (Attr_Z "c0").

Section Sec.

Variable d : vsem.
Notation T := (TD d).

(** one table, [t]: its columns and its rows *)
Definition bs (l : list GenericInstance.attribute) (r : relname) : Fset.set (A T) :=
  match r with Rel s => if String.eqb s "t" then Fset.mk_set (A T) l else Fset.empty (A T) end.

Definition inst (l : list GenericInstance.attribute) (rows : list (list NullValues.value)) (r : relname) : Febag.bag (Fecol.CBag (CTuple T)) :=
  match r with
  | Rel s => if String.eqb s "t"
             then Febag.mk_bag (Fecol.CBag (CTuple T)) (map (fun vs => combine l vs) rows)
             else Febag.empty (Fecol.CBag (CTuple T))
  end.

(** The rows of a stored table are the elements of a bag, in the order of the tuples, which compares the values
    in the order of the names of the attributes: the hypothesis of the theorem (the rows of the two tables are
    related one by one, in the same order) holds here because the two columns grow together. *)
Definition rows := [[VZ 1; VZ 2]; [VZ 3; VZ 4]; [VZ 5; VZ 6]].
Definition f := swap_name "a" "x".

End Sec.

Notation RUN d cols q := (eval_query_list ORN (dialect_of d) (bs d cols) (inst d cols rows) (to_dialect d q)).

(** [SELECT a + 1 AS c0, (SELECT count(u.b) FROM t u WHERE u.a <= t.a) AS x FROM t WHERE a IN (SELECT a FROM t)
    ORDER BY a DESC]: a correlated subquery, an aggregate, [IN], an alias which is the other name *)
Definition q : squery :=
  order_by
    (select_where [as_ (fn "plus" [col a; int 1]) c0;
                   as_ (e_sub (select_where [as_ (agg "count" (col (Attr_Z "v"))) c0]
                                            [from_as (table "t") [(a, Attr_Z "u"); (b, Attr_Z "v")]]
                                            (pred "<=" [col (Attr_Z "u"); col a]))) x]
                  [from_table "t"]
                  (c_in [col a] (select_where [as_ (col a) c0] [from_table "t"] c_true) [c0]))
    [o_by (col a) Desc].

Theorem renamed : forall d,
  RL (TD d) (rename_names f) (rename_names f)
     (eval_query_list ORN (dialect_of d) (bs d [x; b]) (inst d [x; b] rows) (r_q (TD d) relname (rename_names f) (to_dialect d q)))
     (RUN d [a; b] q).
Proof.
intro d; apply eval_rename_names.
- apply swap_name_invol.
- apply swap_name_invol.
- reflexivity.
- intros [s]; unfold bs; destruct (String.eqb s "t"); vm_compute; reflexivity.
- intros [s]; unfold inst; destruct (String.eqb s "t"); apply RLb_RL; vm_compute; reflexivity.
Qed.

(** the renamed query reads the column [x] of the renamed table and names its second item [a] *)
Example rows_named : map (fun t => (dot (TD MySQL) t c0, dot (TD MySQL) t x)) (RUN MySQL [a; b] q) =
  [(VZ 6, VZ 3); (VZ 4, VZ 2); (VZ 2, VZ 1)].
Proof. check. Qed.

Example rows_renamed :
  map (fun t => (dot (TD MySQL) t c0, dot (TD MySQL) t a))
      (eval_query_list ORN (dialect_of MySQL) (bs MySQL [x; b]) (inst MySQL [x; b] rows)
                       (r_q (TD MySQL) relname (rename_names f) (to_dialect MySQL q))) =
  [(VZ 6, VZ 3); (VZ 4, VZ 2); (VZ 2, VZ 1)].
Proof. check. Qed.
