(** * Recursive queries (TODO 3.6): the [CYCLE] rewriting of PostgreSQL, the restrictions *)
Require Import List String ZArith NArith.
Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.
Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax
        Dialects PostgreSQL MySQL SQLite OceanBase SpecRunner.
Import Tuple.
Import ListNotations.
Open Scope string_scope.
Ltac check := vm_compute; reflexivity.
Notation c0 := (Attr_Z "c0").
Notation c1 := (Attr_Z "c1").
Notation c2 := (Attr_Z "c2").
Notation sid := (Attr_Z "sid").
Notation p := (Attr_Z "p").
Notation cyc := (Attr_Z "cyc").
Notation e0 := (Attr_Z "e0").
Notation e1 := (Attr_Z "e1").
Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).
Definition rows_of (d : vsem) (q : squery) (n : nat) : list (list string) :=
  map (fun t => map (fun i => show_value (dot (TD d) t (out_attr i))) (seq 0 n)) (run d q).
Definition accepts (d : vsem) (q : squery) : bool := accepted_by (dialect_of d) (vs_supports d) (to_dialect d q).

(** The graph 1 -> 2 -> 3 -> 1, and the [CYCLE] clause of PostgreSQL written as the manual defines it
    (7.8.2.2): the path of each row is an array, a row whose node is already on its path closes a cycle
    and is not followed.
    [WITH RECURSIVE s(c0, c1, c2) AS (SELECT 1, ARRAY[1], false
                                      UNION ALL
                                      SELECT e.e1, s.p || e.e1, e.e1 = ANY (s.p)
                                      FROM s JOIN edges e ON e.e0 = s.sid WHERE NOT s.cyc)
     SELECT * FROM s] *)
Definition edges := values_ [c0; c1] [[int 1; int 2]; [int 2; int 3]; [int 3; int 1]].
Definition search :=
  with_rec Set_All "s"
    (select_where [as_ (int 1) c0; as_ (fn "array" [int 1]) c1; as_ (cst (NullValues.Value_bool (Some false))) c2] [] c_true)
    (select_where [as_ (col e1) c0; as_ (fn "||" [col p; col e1]) c1; as_ (e_cond (pred "=any" [col e1; col p])) c2]
       [join J_Inner (from_as (table "s") [(c0, sid); (c1, p); (c2, cyc)]) (from_as edges [(c0, e0); (c1, e1)])
             (pred "=" [col e0; col sid])]
       (c_not (pred "=" [col cyc; cst (NullValues.Value_bool (Some true))])))
    (select_where [as_ (col c0) c0; as_ (col c1) c1; as_ (col c2) c2] [from_table "s"] c_true).
Example cycle_rewriting :
  rows_of PostgreSQL search 3
  (* the generic text of the test shows a boolean as [0] / [1] *)
  = [["1"; "{1}"; "0"]; ["2"; "{1,2}"; "0"]; ["3"; "{1,2,3}"; "0"]; ["1"; "{1,2,3,1}"; "1"]].
Proof. check. Qed.

(** an aggregate in the recursive term is rejected by every engine *)
Definition rec_agg :=
  with_rec Set_All "t" (values_ [c0] [[int 1]])
    (select_where [as_ (agg "sum" (col c0)) c0] [from_table "t"] c_true)
    (select_where [as_ (col c0) c0] [from_table "t"] c_true).
Example rec_agg_rejected :
  map (fun d => accepts d rec_agg) [PostgreSQL; MySQL; SQLite; OceanBaseMySQL; OceanBaseOracle]
  = [false; false; false; false; false].
Proof. check. Qed.
