(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Tests of GROUPING SETS, ROLLUP, CUBE and GROUPING.                            *)
(**   The data and the first results are those of the PostgreSQL manual (7.2.4).    *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String ZArith NArith.

Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.

Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax
        Dialects PostgreSQL MySQL SQLite OceanBase SpecRunner.

Import Tuple.
Import ListNotations.
Open Scope string_scope.

Ltac check := vm_compute; reflexivity.

Notation brand := (Attr_string "brand").
Notation size := (Attr_string "size").
Notation sales := (Attr_Z "sales").
Notation c0 := (Attr_Z "c0").
Notation c1 := (Attr_Z "c1").
Notation c2 := (Attr_Z "c2").
Notation c3 := (Attr_Z "c3").

(** items_sold (brand, size, sales): Foo L 10, Foo M 20, Bar M 15, Bar L 5 *)
Definition db : db_state :=
  mk_insert (create_table init_db (Rel "items_sold") [brand; size; sales])
    (Rel "items_sold") [brand; size; sales]
    [ [VS "Foo"; VS "L"; VZ 10]; [VS "Foo"; VS "M"; VZ 20]; 
      [VS "Bar"; VS "M"; VZ 15]; [VS "Bar"; VS "L"; VZ 5] ].

Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ db) (_instance _ db) (to_dialect d q).

(** the rows of [q], whose columns are [c0, c1, ...], are the expected ones, in any order *)
Definition result_is (d : vsem) (q : squery) (n : nat) (expected : list (list string)) : bool :=
  match_unordered 
    (map (fun t => map (fun i => dot (TD d) t (out_attr i)) (seq 0 n)) (run d q)) expected.

Definition items := [from_table "items_sold"].
Definition b := col brand.
Definition z := col size.

Definition sel_grouped g :=
  select_grouped [as_ b c0; as_ z c1; as_ (agg "sum" (col sales)) c2] items g.

(** [GROUP BY GROUPING SETS ((brand), (size), ())] *)
Example grouping_sets : 
  result_is PostgreSQL (sel_grouped (g_sets [[b]; [z]; []])) 3
    [ ["Foo"; "NULL"; "30"]; ["Bar"; "NULL"; "20"]; 
      ["NULL"; "L"; "15"]; ["NULL"; "M"; "35"]; ["NULL"; "NULL"; "50"] ] = true.
Proof. check. Qed.

(** [GROUP BY ROLLUP (brand, size)] *)
Example rollup : 
  result_is PostgreSQL (sel_grouped (g_rollup [b; z])) 3
    [ ["Foo"; "L"; "10"]; ["Foo"; "M"; "20"]; ["Foo"; "NULL"; "30"];
      ["Bar"; "L"; "5"]; ["Bar"; "M"; "15"]; ["Bar"; "NULL"; "20"];
      ["NULL"; "NULL"; "50"] ] = true.
Proof. check. Qed.

(** [GROUP BY CUBE (brand, size)] *)
Example cube : 
  result_is PostgreSQL (sel_grouped (g_cube [b; z])) 3
    [ ["Foo"; "L"; "10"]; ["Foo"; "M"; "20"]; ["Foo"; "NULL"; "30"];
      ["Bar"; "L"; "5"]; ["Bar"; "M"; "15"]; ["Bar"; "NULL"; "20"];
      ["NULL"; "L"; "15"]; ["NULL"; "M"; "35"]; ["NULL"; "NULL"; "50"] ] = true.
Proof. check. Qed.

(** The grouping sets of a [ROLLUP] and of a [CUBE], in the order of the standard. *)
Example rollup_sets_order : rollup_sets [1; 2; 3]%nat = [[1; 2; 3]; [1; 2]; [1]; []]%nat.
Proof. check. Qed.
Example cube_sets_order : cube_sets [1; 2]%nat = [[1; 2]; [1]; [2]; []]%nat.
Proof. check. Qed.

(** [GROUPING(e)] is 1 where [e] is not grouped, 0 where it is. *)
Example grouping_function : 
  result_is PostgreSQL 
    (select_grouped [as_ (agg "sum" (col sales)) c0; as_ (grouping b) c1; as_ (grouping z) c2] 
                    items (g_rollup [b; z])) 3
    [ ["10"; "0"; "0"]; ["20"; "0"; "0"]; ["30"; "0"; "1"]; ["5"; "0"; "0"]; ["15"; "0"; "0"]; 
      ["20"; "0"; "1"]; ["50"; "1"; "1"] ] = true.
Proof. check. Qed.

(** [HAVING GROUPING(brand) = 1] keeps the grand total: the same expression is NULL there. *)
Example grouping_in_having : 
  result_is PostgreSQL 
    (select_full Set_All (s_list [as_ (agg "sum" (col sales)) c0]) items c_true 
                 (g_rollup [b; z]) (pred "=" [grouping b; int 1])) 1
    [ ["50"] ] = true.
Proof. check. Qed.

(** The aggregates see the original values, and the grand total exists on an empty table. *)
Example rollup_empty : 
  result_is PostgreSQL 
    (select_full Set_All (s_list [as_ b c0; as_ count_star c1]) items (pred "=" [int 1; int 2]) 
                 (g_rollup [b]) c_true) 2
    [ ["NULL"; "0"] ] = true.
Proof. check. Qed.

(** The same results in the dialects which have the constructs. *)
Example rollup_in_oceanbase : 
  forallb (fun d => result_is d (sel_grouped (g_rollup [b; z])) 3
    [ ["Foo"; "L"; "10"]; ["Foo"; "M"; "20"]; ["Foo"; "NULL"; "30"];
      ["Bar"; "L"; "5"]; ["Bar"; "M"; "15"]; ["Bar"; "NULL"; "20"];
      ["NULL"; "NULL"; "50"] ]) [OceanBaseMySQL; OceanBaseOracle; MySQL] = true.
Proof. check. Qed.

(** * Which dialect accepts which grouping *)

Definition acceptance (q : squery) := 
  map (fun d => accepted_by (dialect_of d) (to_dialect d q)) 
      [PostgreSQL; MySQL; SQLite; OceanBaseMySQL; OceanBaseOracle].

Example accepted_grouping_sets : 
  acceptance (sel_grouped (g_sets [[b; z]; [b]; []])) = [true; false; false; true; true].
Proof. check. Qed.

Example accepted_rollup : 
  acceptance (sel_grouped (g_rollup [b; z])) = [true; true; false; true; true].
Proof. check. Qed.

Example accepted_cube : 
  acceptance (sel_grouped (g_cube [b; z])) = [true; false; false; true; true].
Proof. check. Qed.

(** * Bare columns: [SELECT brand, size, sum(sales) FROM items_sold GROUP BY brand] *)

Example accepted_bare_column :
  acceptance (sel_grouped (g_by [b])) = [false; false; true; true; false].
Proof. check. Qed.

Example accepted_no_bare_column :
  acceptance (sel_grouped (g_by [b; z])) = [true; true; true; true; true].
Proof. check. Qed.

(** an expression of grouped columns is not bare *)
Example accepted_grouped_expression :
  acceptance (select_grouped [as_ (fn "+" [b; z]) c0] items (g_by [b; z])) = [true; true; true; true; true].
Proof. check. Qed.
