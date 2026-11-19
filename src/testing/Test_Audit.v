(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Regression tests for the audit of the formalisation (see docs/SQL_COVERAGE.md) *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String ZArith.
Require Import Bool3 FlatData ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection 
        Tree Formula Sql SqlExt SqlFull.
Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax.

Import Tuple. 
Import NullValues. 
Import ListNotations.
Open Scope string_scope.

Ltac check := vm_compute; reflexivity.

(** * 1. The values, predicates, functions and aggregates of [NullValues] *)

Definition P s l := interp_predicate (Predicate s) l.
Definition F s l := interp_symbol (Symbol s) l.
Definition G s l := interp_aggregate (Aggregate s) l.
Definition veq v1 v2 := value_eqb v1 v2.

(** Comparisons are defined on all the types, and are UNKNOWN on NULL. *)
Example lt_string : P "<" [VS "abc"; VS "abd"] = true3. Proof. check. Qed.
Example eq_bool : P "=" [VB true; VB true] = true3. Proof. check. Qed.
Example eq_null : P "=" [NullZ; NullZ] = unknown3. Proof. check. Qed.
Example neq_null : P "<>" [VZ 1; NullZ] = unknown3. Proof. check. Qed.
Example lt_mixed : P "<" [VZ 1; VQ 3 2] = true3. Proof. check. Qed.
Example eq_mixed : P "=" [VZ 2; VQ 4 2] = true3. Proof. check. Qed.

(** The IS predicates are never UNKNOWN. *)
Example is_null_1 : P "is null" [NullS] = true3. Proof. check. Qed.
Example is_null_2 : P "is not null" [NullS] = false3. Proof. check. Qed.
Example distinct_1 : P "is distinct from" [NullZ; NullZ] = false3. Proof. check. Qed.
Example distinct_2 : P "is distinct from" [VZ 1; NullZ] = true3. Proof. check. Qed.
Example is_true_1 : P "is true" [NullB] = false3. Proof. check. Qed.
Example is_unknown_1 : P "is unknown" [NullB] = true3. Proof. check. Qed.

Example between_1 : P "between" [VZ 2; VZ 1; VZ 3] = true3. Proof. check. Qed.
Example between_2 : P "between" [VZ 5; VZ 1; NullZ] = unknown3. Proof. check. Qed.
(** [0 BETWEEN 1 AND NULL] is FALSE: [0 >= 1] is. *)
Example between_3 : P "between" [VZ 0; VZ 1; NullZ] = false3. Proof. check. Qed.

Example like_1 : P "like" [VS "formal"; VS "f%m_l"] = true3. Proof. check. Qed.
Example like_2 : P "like" [VS "formal"; VS "f_m%"] = false3. Proof. check. Qed.
Example like_3 : P "like" [VS "100%"; VS "%\%"] = true3. Proof. check. Qed.
Example like_4 : P "not like" [NullS; VS "%"] = unknown3. Proof. check. Qed.

(** [1 IN (2, NULL)] is UNKNOWN, [1 IN (1, NULL)] is TRUE, [1 NOT IN (2, 3)] is TRUE. *)
Example in_1 : P "in" [VZ 1; VZ 2; NullZ] = unknown3. Proof. check. Qed.
Example in_2 : P "in" [VZ 1; VZ 1; NullZ] = true3. Proof. check. Qed.
Example in_3 : P "not in" [VZ 1; VZ 2; VZ 3] = true3. Proof. check. Qed.
(** [(1, NULL) = (2, NULL)] is FALSE, [(1, NULL) = (1, NULL)] is UNKNOWN. *)
Example row_eq_1 : P "row=" [VZ 1; NullZ; VZ 2; NullZ] = false3. Proof. check. Qed.
Example row_eq_2 : P "row=" [VZ 1; NullZ; VZ 1; NullZ] = unknown3. Proof. check. Qed.

(** Arithmetic. *)
Example plus_null : veq (F "+" [VZ 1; NullZ]) NullZ = true. Proof. check. Qed.
Example div_int : veq (F "/" [VZ (-7); VZ 2]) (VZ (-3)) = true. Proof. check. Qed.
Example mod_int : veq (F "%" [VZ (-7); VZ 2]) (VZ (-1)) = true. Proof. check. Qed.
Example div_zero : veq (F "/" [VZ 7; VZ 0]) NullZ = true. Proof. check. Qed.
Example div_num : veq (F "/" [VZ 7; VQ 2 1]) (VQ 7 2) = true. Proof. check. Qed.
Example round_1 : veq (F "round" [VQ 5 2]) (VZ 3) = true. Proof. check. Qed.
Example round_2 : veq (F "round" [VQ (-5) 2]) (VZ (-3)) = true. Proof. check. Qed.
Example floor_1 : veq (F "floor" [VQ (-5) 2]) (VZ (-3)) = true. Proof. check. Qed.
Example trunc_1 : veq (F "trunc" [VQ (-5) 2]) (VZ (-2)) = true. Proof. check. Qed.
Example power_1 : veq (F "power" [VZ 2; VZ 10]) (VZ 1024) = true. Proof. check. Qed.
Example greatest_1 : veq (F "greatest" [VZ 2; NullZ; VZ 5]) (VZ 5) = true. Proof. check. Qed.

(** Conditional expressions. *)
Example coalesce_1 : veq (F "coalesce" [NullZ; VZ 2; VZ 3]) (VZ 2) = true. Proof. check. Qed.
Example nullif_1 : veq (F "nullif" [VZ 2; VZ 2]) NullZ = true. Proof. check. Qed.
Example nullif_2 : veq (F "nullif" [VZ 2; NullZ]) (VZ 2) = true. Proof. check. Qed.
Example case_1 : 
  veq (F "case" [F "<" [VZ 2; VZ 1]; VS "a"; F "is null" [NullZ]; VS "b"; VS "c"]) (VS "b") = true.
Proof. check. Qed.
Example case_2 : veq (F "case" [F "<" [VZ 2; NullZ]; VS "a"]) NullS = true. Proof. check. Qed.

(** The three-valued connectives, on boolean values. *)
Example and_1 : veq (F "and" [VB false; NullB]) (VB false) = true. Proof. check. Qed.
Example and_2 : veq (F "and" [VB true; NullB]) NullB = true. Proof. check. Qed.
Example or_1 : veq (F "or" [VB true; NullB]) (VB true) = true. Proof. check. Qed.
Example not_1 : veq (F "not" [NullB]) NullB = true. Proof. check. Qed.

(** Strings. *)
Example concat_1 : veq (F "||" [VS "ab"; NullS]) NullS = true. Proof. check. Qed.
Example concat_2 : veq (F "concat" [VS "ab"; NullS; VZ 12]) (VS "ab12") = true. Proof. check. Qed.
Example substring_1 : veq (F "substring" [VS "formal"; VZ 2; VZ 3]) (VS "orm") = true. 
Proof. check. Qed.
Example substring_2 : veq (F "substring" [VS "formal"; VZ 0; VZ 3]) (VS "fo") = true. 
Proof. check. Qed.
Example trim_1 : veq (F "trim" [VS "  a b "]) (VS "a b") = true. Proof. check. Qed.
Example replace_1 : veq (F "replace" [VS "banana"; VS "an"; VS "AN"]) (VS "bANANa") = true. 
Proof. check. Qed.
Example position_1 : veq (F "position" [VS "na"; VS "banana"]) (VZ 3) = true. Proof. check. Qed.
Example upper_1 : veq (F "upper" [VS "Sql 92"]) (VS "SQL 92") = true. Proof. check. Qed.

(** Casts. *)
Example cast_1 : veq (F "cast_int" [VS " -42 "]) (VZ (-42)) = true. Proof. check. Qed.
Example cast_2 : veq (F "cast_int" [VS "4x"]) NullZ = true. Proof. check. Qed.
Example cast_3 : veq (F "cast_numeric" [VS "-12.50"]) (VQ (-25) 2) = true. Proof. check. Qed.
Example cast_4 : veq (F "cast_string" [VZ (-42)]) (VS "-42") = true. Proof. check. Qed.
Example cast_5 : veq (F "cast_int" [VQ 7 2]) (VZ 4) = true. Proof. check. Qed.

(** Aggregates: NULLs are ignored, and the aggregate of nothing is NULL, but for
    the counts. *)
Definition vals := [VZ 10; NullZ; VZ 20; VZ 10].

Example count_1 : veq (G "count" vals) (VZ 3) = true. Proof. check. Qed.
Example count_2 : veq (G "count(*)" vals) (VZ 4) = true. Proof. check. Qed.
Example count_3 : veq (G "distinct count" vals) (VZ 2) = true. Proof. check. Qed.
Example count_4 : veq (G "count" []) (VZ 0) = true. Proof. check. Qed.
Example sum_1 : veq (G "sum" vals) (VZ 40) = true. Proof. check. Qed.
Example sum_2 : veq (G "sum" [NullZ; NullZ]) NullZ = true. Proof. check. Qed.
Example sum_3 : veq (G "sum" []) NullZ = true. Proof. check. Qed.
Example sum_4 : veq (G "distinct sum" vals) (VZ 30) = true. Proof. check. Qed.
Example avg_1 : veq (G "avg" vals) (VQ 40 3) = true. Proof. check. Qed.
Example avg_2 : veq (G "avg" [NullZ]) NullQ = true. Proof. check. Qed.
Example min_1 : veq (G "min" vals) (VZ 10) = true. Proof. check. Qed.
Example max_1 : veq (G "max" vals) (VZ 20) = true. Proof. check. Qed.
Example max_2 : veq (G "max" [VZ (-5); NullZ]) (VZ (-5)) = true. Proof. check. Qed.
Example max_3 : veq (G "max" [VS "b"; VS "ab"]) (VS "b") = true. Proof. check. Qed.
Example max_4 : veq (G "max" [NullZ]) NullZ = true. Proof. check. Qed.
Example every_1 : veq (G "every" [VB true; NullB; VB false]) (VB false) = true. Proof. check. Qed.
Example bool_or_1 : veq (G "bool_or" [NullB]) NullB = true. Proof. check. Qed.
Example string_agg_1 : veq (G "group_concat" [VS "a"; NullS; VS "b"]) (VS "a,b") = true. 
Proof. check. Qed.
Example var_1 : veq (G "var_pop" [VZ 1; VZ 2; VZ 3; VZ 4]) (VQ 5 4) = true. Proof. check. Qed.
Example var_2 : veq (G "var_samp" [VZ 1]) NullQ = true. Proof. check. Qed.

(** * 2. The queries of [Sql.v] and of [SqlExt.v]

<<
   t (a, b)        u (c, d)       w (x, s)       e (y)
     1  10           2  NULL        1  one
     1  NULL         3  30
     2  NULL
>>
*)

Notation a := (Attr_Z "a"). 
Notation b := (Attr_Z "b"). 
Notation c := (Attr_Z "c"). 
Notation d := (Attr_Z "d"). 
Notation x := (Attr_Z "x"). 
Notation y := (Attr_Z "y"). 
Notation s := (Attr_string "s").
Notation cnt := (Attr_Z "cnt").
Notation sm := (Attr_Z "sm").
Notation mx := (Attr_Z "mx").
Notation av := (Attr_Q "av").

Definition db : db_state :=
  mk_insert (mk_insert (mk_insert
   (create_table (create_table (create_table (create_table init_db 
      (Rel "t") [a; b]) (Rel "e") [y]) (Rel "u") [c; d]) (Rel "w") [x; s])
   (Rel "t") [a; b] [ [VZ 1; VZ 10]; [VZ 1; NullZ]; [VZ 2; NullZ] ])
   (Rel "u") [c; d] [ [VZ 2; NullZ]; [VZ 3; VZ 30] ])
   (Rel "w") [x; s] [ [VZ 1; VS "one"] ].

Definition tbl r := _From_Item (_Sql_Table (Rel r)) _Att_Ren_Star.
Definition dot_ z := _Sql_Dot z.
Definition agg_ n z := _A_agg (Aggregate n) (__Sql_Dot z).
Definition sel l := __Select_List (map (fun p => _Select_As (fst p) (snd p)) l).

Definition old_returns q atts rows := 
  rows_permb (map (fun l => map (fun a => match Oset.find OAN a l with 
                                          | Some v => v 
                                          | None => NullZ 
                                          end) atts) (eval_sql_query_in_state db q)) rows.

(** With the aggregates of [NullValues], the queries of [Sql.v] get the results of SQL:
    [SELECT count(b), sum(b), max(b), avg(b) FROM t] *)
Example old_aggregates :
  old_returns 
    (_Sql_Select (sel [(agg_ "count" b, cnt); (agg_ "sum" b, sm); (agg_ "max" b, mx); 
                       (agg_ "avg" b, av)])
                 [tbl "t"] _Sql_True (_Group_By nil) _Sql_True)
    [cnt; sm; mx; av] [ [VZ 1; VZ 10; VZ 10; VQ 10 1] ] = true.
Proof. check. Qed.

(** [SELECT a, sum(b), max(b) FROM t GROUP BY a] *)
Example old_group_by :
  old_returns 
    (_Sql_Select (sel [(dot_ a, a); (agg_ "sum" b, sm); (agg_ "max" b, mx)])
                 [tbl "t"] _Sql_True (_Group_By [__Sql_Dot a]) _Sql_True)
    [a; sm; mx] [ [VZ 1; VZ 10; VZ 10]; [VZ 2; NullZ; NullZ] ] = true.
Proof. check. Qed.

(** KNOWN DEVIATION of [Sql.v]: an aggregate query without GROUP BY over an empty
    table has no row, where SQL has one. [SqlFull] has one (see [agg_empty] in
    [Test_SqlFull.v]). *)
Example old_aggregate_empty :
  eval_sql_query_in_state db 
    (_Sql_Select (sel [(agg_ "count" y, cnt)]) [tbl "e"] _Sql_True (_Group_By nil) _Sql_True) = [].
Proof. check. Qed.

(** [SELECT * FROM t WHERE (a, b) NOT IN (SELECT c, d FROM u)]: the comparison of rows is
    component-wise, so that (1, 10) and (1, NULL) differ from (2, NULL) and from (3, 30),
    since their first component definitely differs. (This used to be empty.) *)
Example old_row_not_in :
  old_returns
    (_Sql_Select _Select_Star [tbl "t"]
       (_Sql_Not (_Sql_In [_Select_As (dot_ a) a; _Select_As (dot_ b) b] 
                          (_Sql_Select (sel [(dot_ c, a); (dot_ d, b)]) [tbl "u"] 
                                       _Sql_True _Group_Fine _Sql_True)))
       _Group_Fine _Sql_True)
    [a; b] [ [VZ 1; VZ 10]; [VZ 1; NullZ] ] = true.
Proof. check. Qed.

(** [SELECT * FROM t WHERE (a, b) IN (SELECT c, d FROM u)]: (2, NULL) is compared with 
    (2, NULL), no component definitely differs, so the result is UNKNOWN and the row is
    not returned. *)
Example old_row_in_unknown :
  old_returns
    (_Sql_Select _Select_Star [tbl "t"]
       (_Sql_In [_Select_As (dot_ a) a; _Select_As (dot_ b) b] 
                (_Sql_Select (sel [(dot_ c, a); (dot_ d, b)]) [tbl "u"] 
                             _Sql_True _Group_Fine _Sql_True))
       _Group_Fine _Sql_True) 
    [a; b] [ ] = true.
Proof. check. Qed.

(** The same query, in [SqlFull]. *)
Example full_row_not_in :
  returns_bag db
    (select_star_where [from_table "t"]
       (c_not (c_in [col a; col b] (table "u") [c; d])))
    [a; b] [ [VZ 1; VZ 10]; [VZ 1; NullZ] ] = true.
Proof. check. Qed.

(** [SELECT * FROM t JOIN u ON c = a JOIN w ON x = c - 1]: the condition of the
    second join refers to the first one. [eval_sql_query_ext] used to return no row. *)
Definition TE r := From_Item_Ext (Sql_Table_Ext TNull (Rel r)) (Att_Ren_Star TNull).
Definition eqp l r := 
  Sql_Pred (sql_query_ext TNull relname) (Values.Predicate "=" : predicate TNull) [l; r].
Definition ext_join_chain := 
  Sql_Select_Ext (Select_Star TNull) (TE "t")
    [Join_Item Inner_Join (Sql_Table_Ext TNull (Rel "u")) (Att_Ren_Star TNull) 
               (eqp (dot_ c) (dot_ a));
     Join_Item Inner_Join (Sql_Table_Ext TNull (Rel "w")) (Att_Ren_Star TNull) 
               (eqp (dot_ x) (_A_fun (Symbol "minus") [dot_ c; CstZ (Some 1%Z)]))]
    (Sql_True _ _) (Group_Fine _) (Sql_True _ _).

Example ext_join_order :
  List.length (show_bag_tuples _ (eval_sql_query_ext (_basesort _ db) (_instance _ db) 
                                    unknown3 contains_nulls nil ext_join_chain)) = 1%nat.
Proof. check. Qed.

Example ext_join_order_translation :
  List.length (eval_sql_query_in_state db (sql_query_ext_to_sql_query ext_join_chain)) = 1%nat.
Proof. check. Qed.
