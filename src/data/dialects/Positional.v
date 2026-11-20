(** * The positional view of the results (TODO 6.3, issue I4)

    In SQL a result is a list of columns, which may have the same name ([SELECT a AS x, b AS x]), and [SELECT *]
    over a join keeps every column of both sides. The tuples of [SqlFull.v] are named; the positional view puts
    the select items at the attributes [c0], [c1], ... (the translator of the conformance suites does so), and
    reads a result as its column names, which are metadata and may repeat, and its rows, which are lists of
    values in the order of the columns. *)
Require Import List String ZArith.
Require Import Bool3 FlatData ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection Tree Formula.
Require Import SqlFull Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax Dialects Naming.
Import Tuple.
Import ListNotations.
Open Scope string_scope.

Definition pos_attr (i : nat) := Attr_Z ("c" ++ NullValues.string_of_Z (Z.of_nat i)).

(** a SELECT whose items are given in order with their names: each item is computed at its position *)
Definition select_positional (items : list (string * sexpr)) (lf : list sfrom) (c : scond) : squery :=
  select_where (map (fun p => as_ (snd (fst p)) (pos_attr (snd p))) (combine items (seq 0 (List.length items)))) lf c.

Record presult := mk_presult { pr_names : list string; pr_rows : list (list NullValues.value) }.

(** the result of a positional SELECT, by the dialect [d] *)
Definition eval_positional (d : vsem) (items : list (string * sexpr)) (lf : list sfrom) (c : scond) : presult :=
  let q := select_positional items lf c in
  let rows := eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q) in
  mk_presult (map fst items)
             (map (fun t => map (fun i => dot (TD d) t (pos_attr i)) (seq 0 (List.length items))) rows).

(** an unnamed item takes the name of PostgreSQL's [FigureColname] *)
Definition auto_names (l : list sexpr) : list (string * sexpr) := map (fun e => (pg_colname e, e)) l.
