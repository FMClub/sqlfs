Require Import List String ZArith NArith.
Require Import FiniteSet Values TuplesImpl GenericInstance SqlSyntax SqlFull SqlFullSyntax Dialects
        PostgreSQL MySQL SQLite OceanBase SpecRunner SltRunner.
Import ListNotations.
Open Scope string_scope.
Definition phases_evidence_slt_lang_replace : list slt_phase := [
  ([("t1", [(Attr_Z "x"); (Attr_string "y")], [[VZ (1); VS "true"]; [VZ (0); VS "false"]])], [
    mk_slt_case "slt_lang_replace.test:5" "IT" 1 (select_full Set_All (s_list [(as_ (col (Attr_Z "t1.x")) (Attr_Z "c0")); (as_ (col (Attr_string "t1.y")) (Attr_Z "c1"))]) [(from_as (table "t1") [((Attr_Z "x"), (Attr_Z "t1.x")); ((Attr_string "y"), (Attr_string "t1.y"))])] (pred "=" [(col (Attr_Z "t1.x")); (int (2))]) g_fine c_true) [] "SELECT x, y FROM t1 WHERE x=2"
  ]);
  ([("t1", [(Attr_Z "x"); (Attr_string "y")], [[VZ (1); VS "true"]; [VZ (0); VS "false"]; [VZ (2); VS "insert"]])], [
    mk_slt_case "slt_lang_replace.test:7" "IT" 1 (select_full Set_All (s_list [(as_ (col (Attr_Z "t1.x")) (Attr_Z "c0")); (as_ (col (Attr_string "t1.y")) (Attr_Z "c1"))]) [(from_as (table "t1") [((Attr_Z "x"), (Attr_Z "t1.x")); ((Attr_string "y"), (Attr_string "t1.y"))])] (pred "=" [(col (Attr_Z "t1.x")); (int (2))]) g_fine c_true) ["2"; "insert"] "SELECT x, y FROM t1 WHERE x=2"
  ])
].
Example slt_MySQL_evidence_slt_lang_replace : slt_failures MySQL phases_evidence_slt_lang_replace = [].
Proof. vm_compute. reflexivity. Qed.
