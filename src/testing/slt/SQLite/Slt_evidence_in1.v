Require Import List String ZArith NArith.
Require Import FiniteSet Values TuplesImpl GenericInstance SqlSyntax SqlFull SqlFullSyntax Dialects
        PostgreSQL MySQL SQLite OceanBase SpecRunner SltRunner.
Import ListNotations.
Open Scope string_scope.
Definition phases_evidence_in1 : list slt_phase := [
  ([], [
    mk_slt_case "in1.test:3" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "in" [(int (1)); (int (2))])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 1 IN (2)";
    mk_slt_case "in1.test:4" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "in" [(int (1)); (int (2)); (int (3)); (int (4)); (int (5)); (int (6)); (int (7)); (int (8)); (int (9))])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 1 IN (2,3,4,5,6,7,8,9)";
    mk_slt_case "in1.test:6" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "not in" [(int (1)); (int (2))])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 1 NOT IN (2)";
    mk_slt_case "in1.test:7" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "not in" [(int (1)); (int (2)); (int (3)); (int (4)); (int (5)); (int (6)); (int (7)); (int (8)); (int (9))])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 1 NOT IN (2,3,4,5,6,7,8,9)"
  ]);
  ([("t1", [(Attr_Z "x")], [])], [
    mk_slt_case "in1.test:12" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(int (1))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t1.x")) (Attr_Z "c0"))]) [(from_as (table "t1") [((Attr_Z "x"), (Attr_Z "t1.x"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 1 IN (SELECT * FROM t1)";
    mk_slt_case "in1.test:14" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(int (1))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t1.x")) (Attr_Z "c0"))]) [(from_as (table "t1") [((Attr_Z "x"), (Attr_Z "t1.x"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 1 NOT IN (SELECT * FROM t1)";
    mk_slt_case "in1.test:16" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_Z "t1.x")) (Attr_Z "c0"))]) [(from_as (table "t1") [((Attr_Z "x"), (Attr_Z "t1.x"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT null IN (SELECT * FROM t1)";
    mk_slt_case "in1.test:18" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_Z "t1.x")) (Attr_Z "c0"))]) [(from_as (table "t1") [((Attr_Z "x"), (Attr_Z "t1.x"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT null NOT IN (SELECT * FROM t1)"
  ]);
  ([("t2", [(Attr_Z "y")], [])], [
    mk_slt_case "in1.test:21" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(int (1))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t2.y")) (Attr_Z "c0"))]) [(from_as (table "t2") [((Attr_Z "y"), (Attr_Z "t2.y"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 1 IN (SELECT * FROM t2)";
    mk_slt_case "in1.test:23" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(int (1))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t2.y")) (Attr_Z "c0"))]) [(from_as (table "t2") [((Attr_Z "y"), (Attr_Z "t2.y"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 1 NOT IN (SELECT * FROM t2)";
    mk_slt_case "in1.test:25" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_Z "t2.y")) (Attr_Z "c0"))]) [(from_as (table "t2") [((Attr_Z "y"), (Attr_Z "t2.y"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT null IN (SELECT * FROM t2)";
    mk_slt_case "in1.test:27" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_Z "t2.y")) (Attr_Z "c0"))]) [(from_as (table "t2") [((Attr_Z "y"), (Attr_Z "t2.y"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT null NOT IN (SELECT * FROM t2)"
  ]);
  ([("t3", [(Attr_Z "z")], [])], [
    mk_slt_case "in1.test:30" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(int (1))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t3.z")) (Attr_Z "c0"))]) [(from_as (table "t3") [((Attr_Z "z"), (Attr_Z "t3.z"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 1 IN (SELECT * FROM t3)";
    mk_slt_case "in1.test:32" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(int (1))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t3.z")) (Attr_Z "c0"))]) [(from_as (table "t3") [((Attr_Z "z"), (Attr_Z "t3.z"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 1 NOT IN (SELECT * FROM t3)";
    mk_slt_case "in1.test:34" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_Z "t3.z")) (Attr_Z "c0"))]) [(from_as (table "t3") [((Attr_Z "z"), (Attr_Z "t3.z"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT null IN (SELECT * FROM t3)";
    mk_slt_case "in1.test:36" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_Z "t3.z")) (Attr_Z "c0"))]) [(from_as (table "t3") [((Attr_Z "z"), (Attr_Z "t3.z"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT null NOT IN (SELECT * FROM t3)"
  ]);
  ([("t1", [(Attr_Z "x")], []); ("t2", [(Attr_Z "y")], [])], [
    mk_slt_case "in1.test:37" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(int (1))] (select_full Set_All (s_list [(as_ (fn "+" [(col (Attr_Z "t1.x")); (col (Attr_Z "t2.y"))]) (Attr_Z "c0"))]) [(join J_Inner (from_as (table "t1") [((Attr_Z "x"), (Attr_Z "t1.x"))]) (from_as (table "t2") [((Attr_Z "y"), (Attr_Z "t2.y"))]) c_true)] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 1 IN (SELECT x+y FROM t1, t2)";
    mk_slt_case "in1.test:38" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(int (1))] (select_full Set_All (s_list [(as_ (fn "+" [(col (Attr_Z "t1.x")); (col (Attr_Z "t2.y"))]) (Attr_Z "c0"))]) [(join J_Inner (from_as (table "t1") [((Attr_Z "x"), (Attr_Z "t1.x"))]) (from_as (table "t2") [((Attr_Z "y"), (Attr_Z "t2.y"))]) c_true)] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 1 NOT IN (SELECT x+y FROM t1,t2)";
    mk_slt_case "in1.test:39" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (fn "+" [(col (Attr_Z "t1.x")); (col (Attr_Z "t2.y"))]) (Attr_Z "c0"))]) [(join J_Inner (from_as (table "t1") [((Attr_Z "x"), (Attr_Z "t1.x"))]) (from_as (table "t2") [((Attr_Z "y"), (Attr_Z "t2.y"))]) c_true)] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT null IN (SELECT x+y FROM t1,t2)";
    mk_slt_case "in1.test:40" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (fn "+" [(col (Attr_Z "t1.x")); (col (Attr_Z "t2.y"))]) (Attr_Z "c0"))]) [(join J_Inner (from_as (table "t1") [((Attr_Z "x"), (Attr_Z "t1.x"))]) (from_as (table "t2") [((Attr_Z "y"), (Attr_Z "t2.y"))]) c_true)] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT null NOT IN (SELECT x+y FROM t1,t2)"
  ]);
  ([("t1", [(Attr_Z "x")], [])], [
    mk_slt_case "in1.test:44" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(cst (VD (123) 2))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t1.x")) (Attr_Z "c0"))]) [(from_as (table "t1") [((Attr_Z "x"), (Attr_Z "t1.x"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 1.23 IN (SELECT * FROM t1)";
    mk_slt_case "in1.test:46" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(cst (VD (123) 2))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t1.x")) (Attr_Z "c0"))]) [(from_as (table "t1") [((Attr_Z "x"), (Attr_Z "t1.x"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 1.23 NOT IN (SELECT * FROM t1)";
    mk_slt_case "in1.test:50" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(str "hello")] (select_full Set_All (s_list [(as_ (col (Attr_Z "t1.x")) (Attr_Z "c0"))]) [(from_as (table "t1") [((Attr_Z "x"), (Attr_Z "t1.x"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 'hello' IN (SELECT * FROM t1)";
    mk_slt_case "in1.test:52" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(str "hello")] (select_full Set_All (s_list [(as_ (col (Attr_Z "t1.x")) (Attr_Z "c0"))]) [(from_as (table "t1") [((Attr_Z "x"), (Attr_Z "t1.x"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 'hello' NOT IN (SELECT * FROM t1)"
  ]);
  ([], [
    mk_slt_case "in1.test:59" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "in" [(int (1)); (int (2)); (int (3)); (int (4))])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 1 IN (2,3,4)";
    mk_slt_case "in1.test:60" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "not in" [(int (1)); (int (2)); (int (3)); (int (4))])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 1 NOT IN (2,3,4)";
    mk_slt_case "in1.test:61" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "in" [(str "a"); (str "b"); (str "c"); (str "d")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 'a' IN ('b','c','d')";
    mk_slt_case "in1.test:62" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "not in" [(str "a"); (str "b"); (str "c"); (str "d")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 'a' NOT IN ('b','c','d')"
  ]);
  ([("t4", [(Attr_Z "a")], [[VZ (2)]; [VZ (3)]; [VZ (4)]])], [
    mk_slt_case "in1.test:90" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(int (1))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t4.a")) (Attr_Z "c0"))]) [(from_as (table "t4") [((Attr_Z "a"), (Attr_Z "t4.a"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 1 IN (SELECT * FROM t4)";
    mk_slt_case "in1.test:92" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(int (1))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t4.a")) (Attr_Z "c0"))]) [(from_as (table "t4") [((Attr_Z "a"), (Attr_Z "t4.a"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 1 NOT IN (SELECT * FROM t4)"
  ]);
  ([("t5", [(Attr_Z "b")], [[VZ (2)]; [VZ (3)]; [VZ (4)]])], [
    mk_slt_case "in1.test:94" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(int (1))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t5.b")) (Attr_Z "c0"))]) [(from_as (table "t5") [((Attr_Z "b"), (Attr_Z "t5.b"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 1 IN (SELECT * FROM t5)";
    mk_slt_case "in1.test:96" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(int (1))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t5.b")) (Attr_Z "c0"))]) [(from_as (table "t5") [((Attr_Z "b"), (Attr_Z "t5.b"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 1 NOT IN (SELECT * FROM t5)"
  ]);
  ([("t6", [(Attr_Z "c")], [[VZ (2)]; [VZ (3)]; [VZ (4)]])], [
    mk_slt_case "in1.test:98" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(int (1))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t6.c")) (Attr_Z "c0"))]) [(from_as (table "t6") [((Attr_Z "c"), (Attr_Z "t6.c"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 1 IN (SELECT * FROM t6)";
    mk_slt_case "in1.test:100" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(int (1))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t6.c")) (Attr_Z "c0"))]) [(from_as (table "t6") [((Attr_Z "c"), (Attr_Z "t6.c"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 1 NOT IN (SELECT * FROM t6)"
  ]);
  ([("t7", [(Attr_string "a")], [[VS "b"]; [VS "c"]; [VS "d"]])], [
    mk_slt_case "in1.test:102" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(str "a")] (select_full Set_All (s_list [(as_ (col (Attr_string "t7.a")) (Attr_Z "c0"))]) [(from_as (table "t7") [((Attr_string "a"), (Attr_string "t7.a"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 'a' IN (SELECT * FROM t7)";
    mk_slt_case "in1.test:104" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(str "a")] (select_full Set_All (s_list [(as_ (col (Attr_string "t7.a")) (Attr_Z "c0"))]) [(from_as (table "t7") [((Attr_string "a"), (Attr_string "t7.a"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 'a' NOT IN (SELECT * FROM t7)"
  ]);
  ([("t8", [(Attr_string "c")], [[VS "b"]; [VS "c"]; [VS "d"]])], [
    mk_slt_case "in1.test:106" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(str "a")] (select_full Set_All (s_list [(as_ (col (Attr_string "t8.c")) (Attr_Z "c0"))]) [(from_as (table "t8") [((Attr_string "c"), (Attr_string "t8.c"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 'a' IN (SELECT * FROM t8)";
    mk_slt_case "in1.test:108" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(str "a")] (select_full Set_All (s_list [(as_ (col (Attr_string "t8.c")) (Attr_Z "c0"))]) [(from_as (table "t8") [((Attr_string "c"), (Attr_string "t8.c"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 'a' NOT IN (SELECT * FROM t8)"
  ]);
  ([], [
    mk_slt_case "in1.test:109" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "in" [(int (2)); (int (2)); (int (3)); (int (4)); (cst NullZ)])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 2 IN (2,3,4,null)";
    mk_slt_case "in1.test:110" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "not in" [(int (3)); (int (2)); (int (3)); (int (4)); (cst NullZ)])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 3 NOT IN (2,3,4,null)";
    mk_slt_case "in1.test:111" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "in" [(int (4)); (int (2)); (int (3)); (int (4))])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 4 IN (2,3,4)";
    mk_slt_case "in1.test:112" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "not in" [(int (2)); (int (2)); (int (3)); (int (4))])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 2 NOT IN (2,3,4)";
    mk_slt_case "in1.test:113" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "in" [(str "b"); (str "b"); (str "c"); (str "d")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 'b' IN ('b','c','d')";
    mk_slt_case "in1.test:114" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "not in" [(str "c"); (str "b"); (str "c"); (str "d")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 'c' NOT IN ('b','c','d')";
    mk_slt_case "in1.test:115" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "in" [(str "d"); (str "b"); (str "c"); (cst NullZ); (str "d")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 'd' IN ('b','c',null,'d')";
    mk_slt_case "in1.test:116" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "not in" [(str "b"); (cst NullZ); (str "b"); (str "c"); (str "d")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 'b' NOT IN (null,'b','c','d')"
  ]);
  ([("t4", [(Attr_Z "a")], [[VZ (2)]; [VZ (3)]; [VZ (4)]])], [
    mk_slt_case "in1.test:118" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(int (2))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t4.a")) (Attr_Z "c0"))]) [(from_as (table "t4") [((Attr_Z "a"), (Attr_Z "t4.a"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 2 IN (SELECT * FROM t4)";
    mk_slt_case "in1.test:120" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(int (3))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t4.a")) (Attr_Z "c0"))]) [(from_as (table "t4") [((Attr_Z "a"), (Attr_Z "t4.a"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 3 NOT IN (SELECT * FROM t4)"
  ]);
  ([("t4n", [(Attr_Z "a")], [[VZ (2)]; [VZ (3)]; [VZ (4)]; [NullZ]])], [
    mk_slt_case "in1.test:122" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(int (4))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t4n.a")) (Attr_Z "c0"))]) [(from_as (table "t4n") [((Attr_Z "a"), (Attr_Z "t4n.a"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 4 IN (SELECT * FROM t4n)";
    mk_slt_case "in1.test:124" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(int (2))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t4n.a")) (Attr_Z "c0"))]) [(from_as (table "t4n") [((Attr_Z "a"), (Attr_Z "t4n.a"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 2 NOT IN (SELECT * FROM t4n)"
  ]);
  ([("t5", [(Attr_Z "b")], [[VZ (2)]; [VZ (3)]; [VZ (4)]])], [
    mk_slt_case "in1.test:126" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(int (2))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t5.b")) (Attr_Z "c0"))]) [(from_as (table "t5") [((Attr_Z "b"), (Attr_Z "t5.b"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 2 IN (SELECT * FROM t5)";
    mk_slt_case "in1.test:128" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(int (3))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t5.b")) (Attr_Z "c0"))]) [(from_as (table "t5") [((Attr_Z "b"), (Attr_Z "t5.b"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 3 NOT IN (SELECT * FROM t5)"
  ]);
  ([("t6", [(Attr_Z "c")], [[VZ (2)]; [VZ (3)]; [VZ (4)]])], [
    mk_slt_case "in1.test:130" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(int (2))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t6.c")) (Attr_Z "c0"))]) [(from_as (table "t6") [((Attr_Z "c"), (Attr_Z "t6.c"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 2 IN (SELECT * FROM t6)";
    mk_slt_case "in1.test:132" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(int (3))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t6.c")) (Attr_Z "c0"))]) [(from_as (table "t6") [((Attr_Z "c"), (Attr_Z "t6.c"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 3 NOT IN (SELECT * FROM t6)"
  ]);
  ([("t6n", [(Attr_Z "c")], [[VZ (2)]; [VZ (3)]; [VZ (4)]; [NullZ]])], [
    mk_slt_case "in1.test:134" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(int (4))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t6n.c")) (Attr_Z "c0"))]) [(from_as (table "t6n") [((Attr_Z "c"), (Attr_Z "t6n.c"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 4 IN (SELECT * FROM t6n)";
    mk_slt_case "in1.test:136" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(int (2))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t6n.c")) (Attr_Z "c0"))]) [(from_as (table "t6n") [((Attr_Z "c"), (Attr_Z "t6n.c"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 2 NOT IN (SELECT * FROM t6n)"
  ]);
  ([("t7", [(Attr_string "a")], [[VS "b"]; [VS "c"]; [VS "d"]])], [
    mk_slt_case "in1.test:138" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(str "b")] (select_full Set_All (s_list [(as_ (col (Attr_string "t7.a")) (Attr_Z "c0"))]) [(from_as (table "t7") [((Attr_string "a"), (Attr_string "t7.a"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 'b' IN (SELECT * FROM t7)";
    mk_slt_case "in1.test:140" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(str "c")] (select_full Set_All (s_list [(as_ (col (Attr_string "t7.a")) (Attr_Z "c0"))]) [(from_as (table "t7") [((Attr_string "a"), (Attr_string "t7.a"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 'c' NOT IN (SELECT * FROM t7)"
  ]);
  ([("t7n", [(Attr_string "a")], [[VS "b"]; [VS "c"]; [VS "d"]; [NullS]])], [
    mk_slt_case "in1.test:142" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(str "c")] (select_full Set_All (s_list [(as_ (col (Attr_string "t7n.a")) (Attr_Z "c0"))]) [(from_as (table "t7n") [((Attr_string "a"), (Attr_string "t7n.a"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 'c' IN (SELECT * FROM t7n)";
    mk_slt_case "in1.test:144" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(str "d")] (select_full Set_All (s_list [(as_ (col (Attr_string "t7n.a")) (Attr_Z "c0"))]) [(from_as (table "t7n") [((Attr_string "a"), (Attr_string "t7n.a"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 'd' NOT IN (SELECT * FROM t7n)"
  ]);
  ([("t8", [(Attr_string "c")], [[VS "b"]; [VS "c"]; [VS "d"]])], [
    mk_slt_case "in1.test:146" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(str "b")] (select_full Set_All (s_list [(as_ (col (Attr_string "t8.c")) (Attr_Z "c0"))]) [(from_as (table "t8") [((Attr_string "c"), (Attr_string "t8.c"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 'b' IN (SELECT * FROM t8)";
    mk_slt_case "in1.test:148" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(str "c")] (select_full Set_All (s_list [(as_ (col (Attr_string "t8.c")) (Attr_Z "c0"))]) [(from_as (table "t8") [((Attr_string "c"), (Attr_string "t8.c"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 'c' NOT IN (SELECT * FROM t8)"
  ]);
  ([("t8n", [(Attr_string "c")], [[VS "b"]; [VS "c"]; [VS "d"]; [NullS]])], [
    mk_slt_case "in1.test:150" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(str "c")] (select_full Set_All (s_list [(as_ (col (Attr_string "t8n.c")) (Attr_Z "c0"))]) [(from_as (table "t8n") [((Attr_string "c"), (Attr_string "t8n.c"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["1"] "SELECT 'c' IN (SELECT * FROM t8n)";
    mk_slt_case "in1.test:152" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(str "d")] (select_full Set_All (s_list [(as_ (col (Attr_string "t8n.c")) (Attr_Z "c0"))]) [(from_as (table "t8n") [((Attr_string "c"), (Attr_string "t8n.c"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["0"] "SELECT 'd' NOT IN (SELECT * FROM t8n)"
  ]);
  ([], [
    mk_slt_case "in1.test:153" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "in" [(int (1)); (int (2)); (int (3)); (int (4)); (cst NullZ)])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT 1 IN (2,3,4,null)";
    mk_slt_case "in1.test:154" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "not in" [(int (1)); (int (2)); (int (3)); (int (4)); (cst NullZ)])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT 1 NOT IN (2,3,4,null)";
    mk_slt_case "in1.test:155" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "in" [(str "a"); (str "b"); (str "c"); (cst NullZ); (str "d")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT 'a' IN ('b','c',null,'d')";
    mk_slt_case "in1.test:156" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "not in" [(str "a"); (cst NullZ); (str "b"); (str "c"); (str "d")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT 'a' NOT IN (null,'b','c','d')"
  ]);
  ([("t4n", [(Attr_Z "a")], [[VZ (2)]; [VZ (3)]; [VZ (4)]; [NullZ]])], [
    mk_slt_case "in1.test:158" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(int (1))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t4n.a")) (Attr_Z "c0"))]) [(from_as (table "t4n") [((Attr_Z "a"), (Attr_Z "t4n.a"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT 1 IN (SELECT * FROM t4n)";
    mk_slt_case "in1.test:160" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(int (5))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t4n.a")) (Attr_Z "c0"))]) [(from_as (table "t4n") [((Attr_Z "a"), (Attr_Z "t4n.a"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT 5 NOT IN (SELECT * FROM t4n)"
  ]);
  ([("t6n", [(Attr_Z "c")], [[VZ (2)]; [VZ (3)]; [VZ (4)]; [NullZ]])], [
    mk_slt_case "in1.test:162" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(int (6))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t6n.c")) (Attr_Z "c0"))]) [(from_as (table "t6n") [((Attr_Z "c"), (Attr_Z "t6n.c"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT 6 IN (SELECT * FROM t6n)";
    mk_slt_case "in1.test:164" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(int (7))] (select_full Set_All (s_list [(as_ (col (Attr_Z "t6n.c")) (Attr_Z "c0"))]) [(from_as (table "t6n") [((Attr_Z "c"), (Attr_Z "t6n.c"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT 7 NOT IN (SELECT * FROM t6n)"
  ]);
  ([("t7n", [(Attr_string "a")], [[VS "b"]; [VS "c"]; [VS "d"]; [NullS]])], [
    mk_slt_case "in1.test:166" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(str "a")] (select_full Set_All (s_list [(as_ (col (Attr_string "t7n.a")) (Attr_Z "c0"))]) [(from_as (table "t7n") [((Attr_string "a"), (Attr_string "t7n.a"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT 'a' IN (SELECT * FROM t7n)";
    mk_slt_case "in1.test:168" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(str "e")] (select_full Set_All (s_list [(as_ (col (Attr_string "t7n.a")) (Attr_Z "c0"))]) [(from_as (table "t7n") [((Attr_string "a"), (Attr_string "t7n.a"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT 'e' NOT IN (SELECT * FROM t7n)"
  ]);
  ([("t8n", [(Attr_string "c")], [[VS "b"]; [VS "c"]; [VS "d"]; [NullS]])], [
    mk_slt_case "in1.test:170" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(str "f")] (select_full Set_All (s_list [(as_ (col (Attr_string "t8n.c")) (Attr_Z "c0"))]) [(from_as (table "t8n") [((Attr_string "c"), (Attr_string "t8n.c"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT 'f' IN (SELECT * FROM t8n)";
    mk_slt_case "in1.test:172" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(str "g")] (select_full Set_All (s_list [(as_ (col (Attr_string "t8n.c")) (Attr_Z "c0"))]) [(from_as (table "t8n") [((Attr_string "c"), (Attr_string "t8n.c"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT 'g' NOT IN (SELECT * FROM t8n)"
  ]);
  ([], [
    mk_slt_case "in1.test:173" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "in" [(cst NullZ); (int (2)); (int (3)); (int (4)); (cst NullZ)])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null IN (2,3,4,null)";
    mk_slt_case "in1.test:174" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "not in" [(cst NullZ); (int (2)); (int (3)); (int (4)); (cst NullZ)])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null NOT IN (2,3,4,null)";
    mk_slt_case "in1.test:175" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "in" [(cst NullZ); (int (2)); (int (3)); (int (4))])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null IN (2,3,4)";
    mk_slt_case "in1.test:176" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "not in" [(cst NullZ); (int (2)); (int (3)); (int (4))])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null NOT IN (2,3,4)";
    mk_slt_case "in1.test:177" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "in" [(cst NullZ); (str "b"); (str "c"); (str "d")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null IN ('b','c','d')";
    mk_slt_case "in1.test:178" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "not in" [(cst NullZ); (str "b"); (str "c"); (str "d")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null NOT IN ('b','c','d')";
    mk_slt_case "in1.test:179" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "in" [(cst NullZ); (str "b"); (str "c"); (cst NullZ); (str "d")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null IN ('b','c',null,'d')";
    mk_slt_case "in1.test:180" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "not in" [(cst NullZ); (cst NullZ); (str "b"); (str "c"); (str "d")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null NOT IN (null,'b','c','d')"
  ]);
  ([("t4", [(Attr_Z "a")], [[VZ (2)]; [VZ (3)]; [VZ (4)]])], [
    mk_slt_case "in1.test:182" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_Z "t4.a")) (Attr_Z "c0"))]) [(from_as (table "t4") [((Attr_Z "a"), (Attr_Z "t4.a"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null IN (SELECT * FROM t4)"
  ]);
  ([], [
    mk_slt_case "in1.test:183" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (pred "in" [(cst NullZ); (int (2)); (int (3)); (int (4))])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null IN (2,3,4)"
  ]);
  ([("t4", [(Attr_Z "a")], [[VZ (2)]; [VZ (3)]; [VZ (4)]])], [
    mk_slt_case "in1.test:185" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_Z "t4.a")) (Attr_Z "c0"))]) [(from_as (table "t4") [((Attr_Z "a"), (Attr_Z "t4.a"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null NOT IN (SELECT * FROM t4)"
  ]);
  ([("t4n", [(Attr_Z "a")], [[VZ (2)]; [VZ (3)]; [VZ (4)]; [NullZ]])], [
    mk_slt_case "in1.test:187" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_Z "t4n.a")) (Attr_Z "c0"))]) [(from_as (table "t4n") [((Attr_Z "a"), (Attr_Z "t4n.a"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null IN (SELECT * FROM t4n)";
    mk_slt_case "in1.test:189" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_Z "t4n.a")) (Attr_Z "c0"))]) [(from_as (table "t4n") [((Attr_Z "a"), (Attr_Z "t4n.a"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null NOT IN (SELECT * FROM t4n)"
  ]);
  ([("t5", [(Attr_Z "b")], [[VZ (2)]; [VZ (3)]; [VZ (4)]])], [
    mk_slt_case "in1.test:191" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_Z "t5.b")) (Attr_Z "c0"))]) [(from_as (table "t5") [((Attr_Z "b"), (Attr_Z "t5.b"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null IN (SELECT * FROM t5)";
    mk_slt_case "in1.test:193" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_Z "t5.b")) (Attr_Z "c0"))]) [(from_as (table "t5") [((Attr_Z "b"), (Attr_Z "t5.b"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null NOT IN (SELECT * FROM t5)"
  ]);
  ([("t6", [(Attr_Z "c")], [[VZ (2)]; [VZ (3)]; [VZ (4)]])], [
    mk_slt_case "in1.test:195" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_Z "t6.c")) (Attr_Z "c0"))]) [(from_as (table "t6") [((Attr_Z "c"), (Attr_Z "t6.c"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null IN (SELECT * FROM t6)";
    mk_slt_case "in1.test:197" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_Z "t6.c")) (Attr_Z "c0"))]) [(from_as (table "t6") [((Attr_Z "c"), (Attr_Z "t6.c"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null NOT IN (SELECT * FROM t6)"
  ]);
  ([("t6n", [(Attr_Z "c")], [[VZ (2)]; [VZ (3)]; [VZ (4)]; [NullZ]])], [
    mk_slt_case "in1.test:199" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_Z "t6n.c")) (Attr_Z "c0"))]) [(from_as (table "t6n") [((Attr_Z "c"), (Attr_Z "t6n.c"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null IN (SELECT * FROM t6n)";
    mk_slt_case "in1.test:201" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_Z "t6n.c")) (Attr_Z "c0"))]) [(from_as (table "t6n") [((Attr_Z "c"), (Attr_Z "t6n.c"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null NOT IN (SELECT * FROM t6n)"
  ]);
  ([("t7", [(Attr_string "a")], [[VS "b"]; [VS "c"]; [VS "d"]])], [
    mk_slt_case "in1.test:203" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_string "t7.a")) (Attr_Z "c0"))]) [(from_as (table "t7") [((Attr_string "a"), (Attr_string "t7.a"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null IN (SELECT * FROM t7)";
    mk_slt_case "in1.test:205" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_string "t7.a")) (Attr_Z "c0"))]) [(from_as (table "t7") [((Attr_string "a"), (Attr_string "t7.a"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null NOT IN (SELECT * FROM t7)"
  ]);
  ([("t7n", [(Attr_string "a")], [[VS "b"]; [VS "c"]; [VS "d"]; [NullS]])], [
    mk_slt_case "in1.test:207" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_string "t7n.a")) (Attr_Z "c0"))]) [(from_as (table "t7n") [((Attr_string "a"), (Attr_string "t7n.a"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null IN (SELECT * FROM t7n)";
    mk_slt_case "in1.test:209" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_string "t7n.a")) (Attr_Z "c0"))]) [(from_as (table "t7n") [((Attr_string "a"), (Attr_string "t7n.a"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null NOT IN (SELECT * FROM t7n)"
  ]);
  ([("t8", [(Attr_string "c")], [[VS "b"]; [VS "c"]; [VS "d"]])], [
    mk_slt_case "in1.test:211" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_string "t8.c")) (Attr_Z "c0"))]) [(from_as (table "t8") [((Attr_string "c"), (Attr_string "t8.c"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null IN (SELECT * FROM t8)";
    mk_slt_case "in1.test:213" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_string "t8.c")) (Attr_Z "c0"))]) [(from_as (table "t8") [((Attr_string "c"), (Attr_string "t8.c"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null NOT IN (SELECT * FROM t8)"
  ]);
  ([("t8n", [(Attr_string "c")], [[VS "b"]; [VS "c"]; [VS "d"]; [NullS]])], [
    mk_slt_case "in1.test:215" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_string "t8n.c")) (Attr_Z "c0"))]) [(from_as (table "t8n") [((Attr_string "c"), (Attr_string "t8n.c"))])] c_true g_fine c_true) [(Attr_Z "c0")])) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null IN (SELECT * FROM t8n)";
    mk_slt_case "in1.test:217" "I" 0 (select_full Set_All (s_list [(as_ (e_cond (c_not (c_in [(cst NullZ)] (select_full Set_All (s_list [(as_ (col (Attr_string "t8n.c")) (Attr_Z "c0"))]) [(from_as (table "t8n") [((Attr_string "c"), (Attr_string "t8n.c"))])] c_true g_fine c_true) [(Attr_Z "c0")]))) (Attr_Z "c0"))]) [] c_true g_fine c_true) ["NULL"] "SELECT null NOT IN (SELECT * FROM t8n)"
  ])
].
Example slt_SQLite_evidence_in1 : slt_failures SQLite phases_evidence_in1 = [].
Proof. vm_compute. reflexivity. Qed.
