(** * Set operations (TODO 3.3): type of the columns, multiplicities, NULLs *)
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
Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).
Definition col0 (d : vsem) (q : squery) : list string :=
  map (fun t => show_value (dot (TD d) t (out_attr 0))) (run d q).
Definition one (e : sexpr) := select_where [as_ e c0] [] c_true.
Definition vals (l : list sexpr) := values_ [c0] (map (fun e => [e]) l).

(** [SELECT 1 UNION ALL SELECT 2.5]: a [DECIMAL(2,1)] column in MySQL, so [1] is shown [1.0];
    PostgreSQL's [numeric] keeps the scale of each value *)
Example my_union_scale : col0 MySQL (set_op_ Union Set_All (one (int 1)) (one (cst (VD 25 1)))) = ["1.0"; "2.5"].
Proof. check. Qed.
Example pg_union_scale : col0 PostgreSQL (set_op_ Union Set_All (one (int 1)) (one (cst (VD 25 1)))) = ["1"; "2.5"].
Proof. check. Qed.
(** with a string, the MySQL column is a string: no padding *)
Example my_union_string : col0 MySQL (set_op_ Union Set_All (one (str "a")) (one (cst (VD 25 1)))) = ["a"; "2.5"].
Proof. check. Qed.

(** [EXCEPT ALL] and [INTERSECT ALL]: multiplicities [max (m - n, 0)] and [min (m, n)] *)
Example except_all :
  col0 PostgreSQL (set_op_ Diff Set_All (vals [int 1; int 1; int 1; int 2]) (vals [int 1])) = ["1"; "1"; "2"].
Proof. check. Qed.
Example intersect_all :
  col0 PostgreSQL (set_op_ Inter Set_All (vals [int 1; int 1; int 2]) (vals [int 1; int 1; int 1])) = ["1"; "1"].
Proof. check. Qed.
Example except_distinct :
  col0 PostgreSQL (set_op_ Diff Set_Distinct (vals [int 1; int 1; int 2; int 3]) (vals [int 3])) = ["1"; "2"].
Proof. check. Qed.
(** two NULLs are not distinct in a set operation *)
Example intersect_null :
  col0 PostgreSQL (set_op_ Inter Set_Distinct (vals [cst NullZ; int 1]) (vals [cst NullZ])) = ["NULL"].
Proof. check. Qed.
Example union_null :
  col0 MySQL (set_op_ Union Set_Distinct (vals [cst NullZ; cst NullZ]) (vals [cst NullZ])) = ["NULL"].
Proof. check. Qed.
(** under a case-insensitive collation, ['a'] and ['A'] are one row of a [UNION] (MySQL's default
    collation [utf8mb4_0900_ai_ci]) *)
Example union_collation :
  List.length (col0 MySQL (set_op_ Union Set_Distinct (vals [str "a"]) (vals [str "A"]))) = 1%nat.
Proof. check. Qed.
Example union_binary :
  List.length (col0 PostgreSQL (set_op_ Union Set_Distinct (vals [str "a"]) (vals [str "A"]))) = 2%nat.
Proof. check. Qed.
