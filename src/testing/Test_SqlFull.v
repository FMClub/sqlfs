(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Tests of SqlFull: each example states the result that SQL prescribes for a    *)
(**   query, and is checked by computation.                                         *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String ZArith NArith.

Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.

Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax.

Import Tuple.
Import ListNotations.
Open Scope string_scope.

(** * A database

<<
 emp (name, dept, sal, mgr)          dept (id, dname)        empty (x)
   alice   10    5000  NULL            10  eng
   bob     10    4000  alice           20  ops
   carol   20    4000  alice           30  hr
   dave    20    NULL  carol
   erin    NULL  3000  carol
>>
*)

Notation name := (Attr_string "name").
Notation dept := (Attr_Z "dept").
Notation sal := (Attr_Z "sal").
Notation mgr := (Attr_string "mgr").
Notation id := (Attr_Z "id").
Notation dname := (Attr_string "dname").
Notation x := (Attr_Z "x").

Definition db : db_state :=
  mk_insert
    (mk_insert
       (create_table 
          (create_table (create_table init_db (Rel "emp") [name; dept; sal; mgr])
                        (Rel "dept") [id; dname])
          (Rel "empty") [x])
       (Rel "emp") [name; dept; sal; mgr]
       [ [VS "alice"; VZ 10; VZ 5000; NullS];
         [VS "bob"; VZ 10; VZ 4000; VS "alice"];
         [VS "carol"; VZ 20; VZ 4000; VS "alice"];
         [VS "dave"; VZ 20; NullZ; VS "carol"];
         [VS "erin"; NullZ; VZ 3000; VS "carol"] ])
    (Rel "dept") [id; dname]
    [ [VZ 10; VS "eng"]; [VZ 20; VS "ops"]; [VZ 30; VS "hr"] ].

Notation c := (Attr_Z "c").
Notation c2 := (Attr_Z "c2").
Notation s := (Attr_Z "s").
Notation a := (Attr_Q "a").
Notation mn := (Attr_Z "mn").
Notation mx := (Attr_Z "mx").
Notation lbl := (Attr_string "lbl").

Ltac check := vm_compute; reflexivity.

(** * Aggregates *)

(** [SELECT count( * ) c, count(x) c2, sum(x) s, max(x) mx FROM empty]: an
    aggregate query without GROUP BY has exactly one row, even on an empty table. *)
Example agg_empty :
  returns_bag db
    (select_where [as_ count_star c; as_ (agg "count" (col x)) c2;
                   as_ (agg "sum" (col x)) s; as_ (agg "max" (col x)) mx]
                  [from_table "empty"] c_true)
    [c; c2; s; mx] [ [VZ 0; VZ 0; NullZ; NullZ] ] = true.
Proof. check. Qed.

(** [SELECT count( * ), count(sal), sum(sal), avg(sal), min(sal), max(sal) FROM emp]:
    aggregates ignore NULLs; [avg] of integers is a [numeric] with the scale of [select_div_scale]
    (PostgreSQL prints [4000.0000000000000000]). *)
Example agg_nulls :
  returns_bag db
    (select_where [as_ count_star c; as_ (agg "count" (col sal)) c2;
                   as_ (agg "sum" (col sal)) s; as_ (agg "avg" (col sal)) a;
                   as_ (agg "min" (col sal)) mn; as_ (agg "max" (col sal)) mx]
                  [from_table "emp"] c_true)
    [c; c2; s; a; mn; mx] [ [VZ 5; VZ 4; VZ 16000; VDi 4000 16; VZ 3000; VZ 5000] ] = true.
Proof. check. Qed.

(** [SELECT dept, count( * ) c, sum(sal) s FROM emp GROUP BY dept]: the NULLs
    form a group. *)
Example group_by_null :
  returns_bag db
    (select_group [as_ (col dept) dept; as_ count_star c; as_ (agg "sum" (col sal)) s]
                  [from_table "emp"] c_true [col dept] c_true)
    [dept; c; s] 
    [ [VZ 10; VZ 2; VZ 9000]; [VZ 20; VZ 2; VZ 4000]; [NullZ; VZ 1; VZ 3000] ] = true.
Proof. check. Qed.

(** [SELECT dept FROM emp GROUP BY dept HAVING count( * ) > 1 AND min(sal) >= 4000] *)
Example having :
  returns_bag db
    (select_group [as_ (col dept) dept] [from_table "emp"] c_true [col dept]
                  (c_and (pred ">" [count_star; int 1]) 
                         (pred ">=" [agg "min" (col sal); int 4000])))
    [dept] [ [VZ 10]; [VZ 20] ] = true.
Proof. check. Qed.

(** [SELECT count(DISTINCT sal) c, count(sal) FILTER (WHERE dept = 10) c2, 
           sum(DISTINCT sal) s FROM emp] *)
Example agg_distinct_filter :
  returns_bag db
    (select_where [as_ (agg_distinct "count" (col sal)) c;
                   as_ (agg_filter "count" (col sal) (pred "=" [col dept; int 10])) c2;
                   as_ (agg_distinct "sum" (col sal)) s]
                  [from_table "emp"] c_true)
    [c; c2; s] [ [VZ 3; VZ 2; VZ 12000] ] = true.
Proof. check. Qed.

(** An aggregate of the outer block inside a subquery:
    [SELECT dept FROM emp GROUP BY dept 
     HAVING 2 = (SELECT count(name) FROM dept WHERE id = dept)].
    [count(name)] counts the rows of the group of [emp]. *)
Example correlated_aggregate :
  returns_bag db
    (select_group [as_ (col dept) dept] [from_table "emp"] c_true [col dept]
       (pred "=" [int 2; 
                  e_sub (select_where [as_ (agg "count" (col name)) c] [from_table "dept"]
                                      (pred "=" [col id; col dept]))]))
    [dept] [ [VZ 10]; [VZ 20] ] = true.
Proof. check. Qed.

(** * Three-valued logic *)

(** [SELECT name FROM emp WHERE sal > 3500] *)
Example where_unknown_1 :
  returns_bag db
    (select_where [as_ (col name) name] [from_table "emp"] (pred ">" [col sal; int 3500]))
    [name] [ [VS "alice"]; [VS "bob"]; [VS "carol"] ] = true.
Proof. check. Qed.

(** [SELECT name FROM emp WHERE NOT (sal > 3500)]: dave is in neither result. *)
Example where_unknown_2 :
  returns_bag db
    (select_where [as_ (col name) name] [from_table "emp"] 
                  (c_not (pred ">" [col sal; int 3500])))
    [name] [ [VS "erin"] ] = true.
Proof. check. Qed.

(** [SELECT name FROM emp WHERE sal IS NULL OR dept IS NOT DISTINCT FROM NULL] *)
Example is_null :
  returns_bag db
    (select_where [as_ (col name) name] [from_table "emp"] 
                  (c_or (pred "is null" [col sal]) 
                        (pred "is not distinct from" [col dept; cst NullZ])))
    [name] [ [VS "dave"]; [VS "erin"] ] = true.
Proof. check. Qed.

(** [SELECT name FROM emp 
     WHERE name LIKE '%a%' AND sal BETWEEN 4000 AND 5000 AND dept IN (10, 30)] *)
Example like_between_in :
  returns_bag db
    (select_where [as_ (col name) name] [from_table "emp"] 
                  (c_and (pred "like" [col name; str "%a%"])
                         (c_and (pred "between" [col sal; int 4000; int 5000])
                                (pred "in" [col dept; int 10; int 30]))))
    [name] [ [VS "alice"] ] = true.
Proof. check. Qed.

(** * Subqueries *)

Definition emp_depts := select_where [as_ (col dept) dept] [from_table "emp"] c_true.

(** [SELECT dname FROM dept WHERE id NOT IN (SELECT dept FROM emp)]: empty, since
    the subquery contains a NULL. *)
Example not_in_null :
  returns_bag db
    (select_where [as_ (col dname) dname] [from_table "dept"] 
                  (c_not (c_in [col id] emp_depts [dept])))
    [dname] [ ] = true.
Proof. check. Qed.

(** [SELECT dname FROM dept 
     WHERE id NOT IN (SELECT dept FROM emp WHERE dept IS NOT NULL)] *)
Example not_in :
  returns_bag db
    (select_where [as_ (col dname) dname] [from_table "dept"] 
       (c_not (c_in [col id] 
                    (select_where [as_ (col dept) dept] [from_table "emp"] 
                                  (pred "is not null" [col dept])) [dept])))
    [dname] [ [VS "hr"] ] = true.
Proof. check. Qed.

(** [SELECT name FROM emp WHERE (dept, sal) NOT IN (SELECT id, NULL FROM dept)]:
    a row comparison is FALSE as soon as one of its components is, so that the 
    employee without department is returned. *)
Example row_not_in :
  returns_bag db
    (select_where [as_ (col name) name] [from_table "emp"] 
       (c_not (c_in [col dept; col sal] 
                    (select_where [as_ (col id) id; as_ (cst NullZ) x] [from_table "dept"] c_true)
                    [id; x])))
    [name] [ ] = true.
Proof. check. Qed.

(** [SELECT name FROM emp WHERE (dept, sal) NOT IN (SELECT 30, NULL)] *)
Example row_not_in_2 :
  returns_bag db
    (select_where [as_ (col name) name] [from_table "emp"] 
       (c_not (c_in [col dept; col sal] 
                    (select_where [as_ (int 30) id; as_ (cst NullZ) x] [] c_true)
                    [id; x])))
    [name] [ [VS "alice"]; [VS "bob"]; [VS "carol"]; [VS "dave"] ] = true.
Proof. check. Qed.

(** [SELECT dname FROM dept WHERE EXISTS (SELECT * FROM emp WHERE dept = id)] *)
Example exists_correlated :
  returns_bag db
    (select_where [as_ (col dname) dname] [from_table "dept"] 
       (c_exists (select_star_where [from_table "emp"] (pred "=" [col dept; col id]))))
    [dname] [ [VS "eng"]; [VS "ops"] ] = true.
Proof. check. Qed.

(** [SELECT dname, (SELECT count( * ) FROM emp WHERE dept = id) c,
                   (SELECT max(sal) FROM emp WHERE dept = id) mx FROM dept] *)
Example scalar_subquery :
  returns_bag db
    (select_where 
       [as_ (col dname) dname;
        as_ (e_sub (select_where [as_ count_star c] [from_table "emp"] 
                                 (pred "=" [col dept; col id]))) c;
        as_ (e_sub (select_where [as_ (agg "max" (col sal)) mx] [from_table "emp"] 
                                 (pred "=" [col dept; col id]))) mx]
       [from_table "dept"] c_true)
    [dname; c; mx] 
    [ [VS "eng"; VZ 2; VZ 5000]; [VS "ops"; VZ 2; VZ 4000]; [VS "hr"; VZ 0; NullZ] ] = true.
Proof. check. Qed.

(** [SELECT name FROM emp WHERE sal >= ALL (SELECT sal FROM emp WHERE dept = 20)]:
    one of the salaries of the department 20 is NULL, the condition is never TRUE. *)
Example quant_all :
  returns_bag db
    (select_where [as_ (col name) name] [from_table "emp"] 
       (c_all ">=" [col sal] 
              (select_where [as_ (col sal) s] [from_table "emp"] (pred "=" [col dept; int 20]))
              [s]))
    [name] [ ] = true.
Proof. check. Qed.

(** [SELECT name FROM emp WHERE sal > ANY (SELECT sal FROM emp WHERE dept = 20)] *)
Example quant_any :
  returns_bag db
    (select_where [as_ (col name) name] [from_table "emp"] 
       (c_any ">" [col sal] 
              (select_where [as_ (col sal) s] [from_table "emp"] (pred "=" [col dept; int 20]))
              [s]))
    [name] [ [VS "alice"] ] = true.
Proof. check. Qed.

(** * Joins *)

Definition on_dept := pred "=" [col dept; col id].
Definition name_dname jt :=
  select_where [as_ (col name) name; as_ (col dname) dname]
               [join jt (from_table "emp") (from_table "dept") on_dept] c_true.

Example inner_join :
  returns_bag db (name_dname J_Inner) [name; dname]
    [ [VS "alice"; VS "eng"]; [VS "bob"; VS "eng"]; 
      [VS "carol"; VS "ops"]; [VS "dave"; VS "ops"] ] = true.
Proof. check. Qed.

Example left_join :
  returns_bag db (name_dname J_Left) [name; dname]
    [ [VS "alice"; VS "eng"]; [VS "bob"; VS "eng"]; 
      [VS "carol"; VS "ops"]; [VS "dave"; VS "ops"]; [VS "erin"; NullS] ] = true.
Proof. check. Qed.

Example right_join :
  returns_bag db (name_dname J_Right) [name; dname]
    [ [VS "alice"; VS "eng"]; [VS "bob"; VS "eng"]; 
      [VS "carol"; VS "ops"]; [VS "dave"; VS "ops"]; [NullS; VS "hr"] ] = true.
Proof. check. Qed.

Example full_join :
  returns_bag db (name_dname J_Full) [name; dname]
    [ [VS "alice"; VS "eng"]; [VS "bob"; VS "eng"]; [VS "carol"; VS "ops"]; 
      [VS "dave"; VS "ops"]; [VS "erin"; NullS]; [NullS; VS "hr"] ] = true.
Proof. check. Qed.

(** A self join, with a renaming: 
    [SELECT e.name, m.name AS mgr FROM emp e JOIN emp m ON e.mgr = m.name 
     WHERE e.sal < m.sal] *)
Notation m_name := (Attr_string "m.name").
Notation m_sal := (Attr_Z "m.sal").

Example self_join :
  returns_bag db
    (select_where [as_ (col name) name; as_ (col m_name) mgr]
       [join J_Inner (from_table "emp") 
             (from_as (table "emp") [(name, m_name); (sal, m_sal)])
             (pred "=" [col mgr; col m_name])]
       (pred "<" [col sal; col m_sal]))
    [name; mgr] [ [VS "bob"; VS "alice"]; [VS "carol"; VS "alice"]; [VS "erin"; VS "carol"] ] = true.
Proof. check. Qed.

(** Three items: the condition of the second join refers to the first item. *)
Example join_chain :
  returns_bag db
    (select_where [as_ (col name) name; as_ (col dname) dname; as_ (col m_sal) m_sal]
       [join J_Left 
             (join J_Inner (from_table "emp") (from_table "dept") on_dept)
             (from_as (table "emp") [(name, m_name); (sal, m_sal)])
             (pred "=" [col mgr; col m_name])]
       c_true)
    [name; dname; m_sal] 
    [ [VS "alice"; VS "eng"; NullZ]; [VS "bob"; VS "eng"; VZ 5000]; 
      [VS "carol"; VS "ops"; VZ 5000]; [VS "dave"; VS "ops"; VZ 4000] ] = true.
Proof. check. Qed.

(** [SELECT dname, name FROM dept JOIN LATERAL 
       (SELECT name FROM emp WHERE dept = id ORDER BY sal DESC NULLS LAST LIMIT 1) ON TRUE]:
    the best paid employee of each department. *)
Example lateral_join :
  returns_bag db
    (select_where [as_ (col dname) dname; as_ (col name) name]
       [join_lateral J_Inner (from_table "dept")
          (from_query 
             (order_limit (select_where [as_ (col name) name] [from_table "emp"] on_dept)
                          [o_by_nulls (col sal) Desc Nulls_Last] None (Some 1%N)))
          c_true]
       c_true)
    [dname; name] [ [VS "eng"; VS "alice"]; [VS "ops"; VS "carol"] ] = true.
Proof. check. Qed.

(** * DISTINCT and set operations *)

Example distinct :
  returns_bag db (select_distinct [as_ (col sal) sal] [from_table "emp"] c_true)
    [sal] [ [VZ 5000]; [VZ 4000]; [NullZ]; [VZ 3000] ] = true.
Proof. check. Qed.

Definition sals d := 
  select_where [as_ (col sal) sal] [from_table "emp"] (pred "=" [col dept; int d]).

(** 10: 5000, 4000    20: 4000, NULL *)
Example union_all :
  returns_bag db (set_op_ Union Set_All (sals 10) (sals 20)) [sal]
    [ [VZ 5000]; [VZ 4000]; [VZ 4000]; [NullZ] ] = true.
Proof. check. Qed.

Example union_distinct :
  returns_bag db (set_op_ Union Set_Distinct (sals 10) (sals 20)) [sal]
    [ [VZ 5000]; [VZ 4000]; [NullZ] ] = true.
Proof. check. Qed.

Example intersect :
  returns_bag db (set_op_ Inter Set_Distinct (sals 10) (sals 20)) [sal] [ [VZ 4000] ] = true.
Proof. check. Qed.

Example except :
  returns_bag db (set_op_ Diff Set_Distinct (sals 20) (sals 10)) [sal] [ [NullZ] ] = true.
Proof. check. Qed.

(** [EXCEPT ALL] subtracts the multiplicities, [EXCEPT] does not. *)
Definition all_sals := select_where [as_ (col sal) sal] [from_table "emp"] c_true.

Example except_all :
  returns_bag db (set_op_ Diff Set_All all_sals (sals 10)) [sal]
    [ [VZ 4000]; [NullZ]; [VZ 3000] ] = true.
Proof. check. Qed.

Example except_distinct :
  returns_bag db (set_op_ Diff Set_Distinct all_sals (sals 10)) [sal]
    [ [NullZ]; [VZ 3000] ] = true.
Proof. check. Qed.

(** * ORDER BY, OFFSET, LIMIT *)

(** [SELECT name FROM emp ORDER BY sal DESC, name]: by default, NULLs are larger
    than the other values. *)
Example order_by_default :
  returns_list db
    (order_by (select_where [as_ (col name) name] [from_table "emp"] c_true)
              [o_by (col sal) Desc; o_by (col name) Asc])
    [name] [ [VS "dave"]; [VS "alice"]; [VS "bob"]; [VS "carol"]; [VS "erin"] ] = true.
Proof. check. Qed.

(** [SELECT name FROM emp ORDER BY sal DESC NULLS LAST, name DESC OFFSET 1 LIMIT 3] *)
Example order_by_limit :
  returns_list db
    (order_limit (select_where [as_ (col name) name] [from_table "emp"] c_true)
                 [o_by_nulls (col sal) Desc Nulls_Last; o_by (col name) Desc] 
                 (Some 1%N) (Some 3%N))
    [name] [ [VS "carol"]; [VS "bob"]; [VS "erin"] ] = true.
Proof. check. Qed.

(** [SELECT dept, count( * ) c FROM emp GROUP BY dept ORDER BY sum(sal) DESC NULLS LAST, c]:
    ordering by an aggregate which is not in the select list. *)
Example order_by_aggregate :
  returns_list db
    (order_by (select_group [as_ (col dept) dept; as_ count_star c] 
                            [from_table "emp"] c_true [col dept] c_true)
              [o_by_nulls (agg "sum" (col sal)) Desc Nulls_Last; o_by (col c) Asc])
    [dept; c] [ [VZ 10; VZ 2]; [VZ 20; VZ 2]; [NullZ; VZ 1] ] = true.
Proof. check. Qed.

(** [(SELECT sal FROM emp WHERE dept = 10 UNION SELECT sal FROM emp WHERE dept = 20)
     ORDER BY sal NULLS FIRST] *)
Example order_by_union :
  returns_list db
    (order_by (set_op_ Union Set_Distinct (sals 10) (sals 20)) 
              [o_by_nulls (col sal) Asc Nulls_First])
    [sal] [ [NullZ]; [VZ 4000]; [VZ 5000] ] = true.
Proof. check. Qed.

(** * Expressions *)

(** [SELECT name, CASE WHEN sal >= 4500 THEN 'high' WHEN sal >= 3500 THEN 'mid' 
                       ELSE 'low' END lbl, 
            coalesce(sal, 0) / 1000 s FROM emp] *)
Example case_coalesce :
  returns_bag db
    (select_where 
       [as_ (col name) name;
        as_ (e_case (pred ">=" [col sal; int 4500]) (str "high")
                    (e_case (pred ">=" [col sal; int 3500]) (str "mid") (str "low"))) lbl;
        as_ (fn "/" [fn "coalesce" [col sal; int 0]; int 1000]) s]
       [from_table "emp"] c_true)
    [name; lbl; s] 
    [ [VS "alice"; VS "high"; VZ 5]; [VS "bob"; VS "mid"; VZ 4]; [VS "carol"; VS "mid"; VZ 4];
      [VS "dave"; VS "low"; VZ 0]; [VS "erin"; VS "low"; VZ 3] ] = true.
Proof. check. Qed.

(** The arithmetic over a NULL is NULL; an integer is promoted to a numeric: 
    [SELECT sal / NULL c, sal + NULL s, sal / 3.0 a FROM emp WHERE name = 'alice'] *)
Example arithmetic :
  returns_bag db
    (select_where 
       [as_ (fn "/" [col sal; cst NullZ]) c; as_ (fn "+" [col sal; cst NullZ]) s;
        as_ (fn "/" [col sal; cst (VQ 3 1)]) a]
       [from_table "emp"] (pred "=" [col name; str "alice"]))
    [c; s; a] [ [NullZ; NullZ; VQ 5000 3] ] = true.
Proof. check. Qed.

(** Division by zero is an error in PostgreSQL: the query fails, also when the failing value is
    not selected ([SELECT name FROM emp WHERE sal / 0 > 1]), but not when the row is filtered out
    before by a condition which decides ([... WHERE false AND sal / 0 > 1]). *)
Definition fails q :=
  match eval_query_result ORN TNull_PostgreSQL (_basesort _ db) (_instance _ db) q with
  | QR_Error _ => true
  | QR_Rows _ _ => false
  end.

Example division_by_zero_fails :
  fails (select_where [as_ (fn "/" [col sal; int 0]) c] [from_table "emp"] c_true) = true.
Proof. check. Qed.

Example division_by_zero_in_where_fails :
  fails (select_where [as_ (col name) name] [from_table "emp"] (pred ">" [fn "/" [col sal; int 0]; int 1])) = true.
Proof. check. Qed.

Example decided_conjunction_does_not_fail :
  fails (select_where [as_ (col name) name] [from_table "emp"] 
           (c_and (pred "=" [int 1; int 2]) (pred ">" [fn "/" [col sal; int 0]; int 1]))) = false.
Proof. check. Qed.

(** [COALESCE] does not evaluate the arguments after the first non-NULL one, a [CASE] the branch it
    does not take *)
Example lazy_coalesce :
  fails (select_where [as_ (fn "coalesce" [col sal; fn "/" [int 1; int 0]]) c] [from_table "emp"] 
           (pred "=" [col name; str "alice"])) = false.
Proof. check. Qed.

Example lazy_case :
  fails (select_where [as_ (e_case (pred "=" [int 1; int 1]) (int 1) (fn "/" [int 1; int 0])) c] [from_table "emp"] c_true) = false.
Proof. check. Qed.

(** an aggregate over a failed value fails, even [count( * )] over a failed row *)
Example failed_row_counted :
  fails (select_where [as_ (agg "count" (int 1)) c] [from_table "emp"] (pred ">" [fn "/" [col sal; int 0]; int 1])) = true.
Proof. check. Qed.

(** a scalar subquery with several rows fails (PostgreSQL, MySQL; SQLite takes the first row) *)
Example scalar_subquery_rows :
  fails (select_where [as_ (e_sub (select_where [as_ (col sal) sal] [from_table "emp"] c_true)) c] [from_table "emp"] c_true) = true.
Proof. check. Qed.

(** [SELECT upper(substring(name FROM 1 FOR 1)) || substring(name FROM 2) lbl, 
            length(name) c, name LIKE '_a%' AS b FROM emp WHERE dept = 20] *)
Notation b := (Attr_bool "b").

Example strings :
  returns_bag db
    (select_where 
       [as_ (fn "||" [fn "upper" [fn "substring" [col name; int 1; int 1]];
                      fn "substring" [col name; int 2]]) lbl;
        as_ (fn "length" [col name]) c;
        as_ (e_cond (pred "like" [col name; str "_a%"])) b]
       [from_table "emp"] (pred "=" [col dept; int 20]))
    [lbl; c; b] [ [VS "Carol"; VZ 5; VB true]; [VS "Dave"; VZ 4; VB true] ] = true.
Proof. check. Qed.

(** A condition as a value, and a value as a condition:
    [SELECT name, sal > 3500 AS b FROM emp WHERE (sal > 3500) IS NOT TRUE] *)
Example boolean_values :
  returns_bag db
    (select_where 
       [as_ (col name) name; as_ (e_cond (pred ">" [col sal; int 3500])) b]
       [from_table "emp"] 
       (pred "is not true" [e_cond (pred ">" [col sal; int 3500])]))
    [name; b] [ [VS "dave"; NullB]; [VS "erin"; VB false] ] = true.
Proof. check. Qed.

(** * VALUES and WITH *)

(** [VALUES (1, 'one'), (2, NULL)] *)
Example values :
  returns_bag db (values_ [x; lbl] [ [int 1; str "one"]; [int 2; cst NullS] ]) [x; lbl]
    [ [VZ 1; VS "one"]; [VZ 2; NullS] ] = true.
Proof. check. Qed.

(** [WITH big AS (SELECT dept, sum(sal) s FROM emp GROUP BY dept)
     SELECT dname FROM dept, big WHERE id = dept AND s = (SELECT max(s) FROM big)] *)
Example with_cte :
  returns_bag db
    (with_ "big" 
       (select_group [as_ (col dept) dept; as_ (agg "sum" (col sal)) s] 
                     [from_table "emp"] c_true [col dept] c_true)
       (select_where [as_ (col dname) dname] [from_table "dept"; from_table "big"]
          (c_and on_dept
                 (pred "=" [col s; e_sub (select_where [as_ (agg "max" (col s)) mx] 
                                                       [from_table "big"] c_true)]))))
    [dname] [ [VS "eng"] ] = true.
Proof. check. Qed.

(** * Window functions *)

Notation rn := (Attr_Z "rn").
Notation rk := (Attr_Z "rk").
Notation drk := (Attr_Z "drk").
Notation run := (Attr_Z "run").
Notation prev := (Attr_Z "prev").

Definition emp_sal := 
  select_where [as_ (col name) name; as_ (col dept) dept; as_ (col sal) sal] 
               [from_table "emp"] (pred "is not null" [col sal]).

(** [SELECT name, row_number() OVER w rn, rank() OVER w rk, dense_rank() OVER w drk
     FROM emp WHERE sal IS NOT NULL WINDOW w AS (ORDER BY sal DESC)] *)
Example ranking :
  returns_bag db
    (select_where [as_ (col name) name; as_ (col rn) rn; as_ (col rk) rk; as_ (col drk) drk]
       [from_query 
          (window emp_sal [w_as w_row_number [] [o_by (col sal) Desc; o_by (col name) Asc] rn;
                           w_as w_rank [] [o_by (col sal) Desc] rk;
                           w_as w_dense_rank [] [o_by (col sal) Desc] drk])]
       c_true)
    [name; rn; rk; drk] 
    [ [VS "alice"; VZ 1; VZ 1; VZ 1]; [VS "bob"; VZ 2; VZ 2; VZ 2]; 
      [VS "carol"; VZ 3; VZ 2; VZ 2]; [VS "erin"; VZ 4; VZ 4; VZ 3] ] = true.
Proof. check. Qed.

(** [SELECT name, sum(sal) OVER (ORDER BY sal) run,
            sum(sal) OVER (PARTITION BY dept) s,
            lag(sal, 1, 0) OVER (ORDER BY sal, name) prev
     FROM emp WHERE sal IS NOT NULL]: 
    with the default frame, the peers of the current row are in the running sum. *)
Example window_aggregates :
  returns_bag db
    (select_where [as_ (col name) name; as_ (col run) run; as_ (col s) s; as_ (col prev) prev]
       [from_query 
          (window emp_sal 
             [w_as (w_agg "sum" (col sal) default_frame) [] [o_by (col sal) Asc] run;
              w_as (w_agg "sum" (col sal) default_frame) [col dept] [] s;
              w_as (w_lag (col sal) 1 (int 0)) [] [o_by (col sal) Asc; o_by (col name) Asc] prev])]
       c_true)
    [name; run; s; prev] 
    [ [VS "erin"; VZ 3000; VZ 3000; VZ 0]; [VS "bob"; VZ 11000; VZ 9000; VZ 3000]; 
      [VS "carol"; VZ 11000; VZ 4000; VZ 4000]; [VS "alice"; VZ 16000; VZ 9000; VZ 4000] ] = true.
Proof. check. Qed.

(** [SELECT name, sum(sal) OVER (ORDER BY sal, name ROWS BETWEEN 1 PRECEDING AND CURRENT ROW) run
     FROM emp WHERE sal IS NOT NULL] *)
Example window_rows_frame :
  returns_bag db
    (select_where [as_ (col name) name; as_ (col run) run]
       [from_query 
          (window emp_sal 
             [w_as (w_agg "sum" (col sal) (Frame_Rows (Preceding 1) Current_Row)) [] 
                   [o_by (col sal) Asc; o_by (col name) Asc] run])]
       c_true)
    [name; run] 
    [ [VS "erin"; VZ 3000]; [VS "bob"; VZ 7000]; [VS "carol"; VZ 8000]; [VS "alice"; VZ 9000] ] 
  = true.
Proof. check. Qed.

(** * Sorts *)

Example sort_join : 
  sort_is db (select_star_where [join J_Left (from_table "emp") (from_table "dept") on_dept] c_true)
          [name; dept; sal; mgr; id; dname] = true.
Proof. check. Qed.

Example sort_window : sort_is db (window emp_sal [w_as w_rank [] [] rk]) [name; dept; sal; rk] = true.
Proof. check. Qed.
