(** * Oracle-mode derived forms (TODO 4.9): [CONNECT BY], [ROWNUM], [PIVOT], [UNPIVOT] *)
Require Import List String ZArith NArith.
Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.
Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax
        Dialects PostgreSQL MySQL SQLite OceanBase SpecRunner.
Import Tuple.
Import ListNotations.
Open Scope string_scope.
Ltac check := vm_compute; reflexivity.
Notation id := (Attr_Z "id").
Notation mgr := (Attr_Z "mgr").
Notation name := (Attr_string "name").
Notation pid := (Attr_Z "pid").
Notation lvl := (Attr_Z "lvl").
Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).
Definition rows (d : vsem) (q : squery) (atts : list _) : list (list string) :=
  map (fun t => map (fun a => show_value (dot (TD d) t a)) atts) (run d q).

(** [SELECT name, LEVEL FROM emp START WITH mgr IS NULL CONNECT BY PRIOR id = mgr] *)
Definition emp := values_ [id; mgr; name] [[int 1; cst NullZ; str "KING"]; [int 2; int 1; str "JONES"];
                                           [int 3; int 2; str "SCOTT"]; [int 4; int 1; str "BLAKE"]].
Example hierarchy :
  rows OceanBaseOracle (connect_by "h" emp [id; mgr; name] [(id, pid)] lvl
                          (pred "is null" [col mgr]) (pred "=" [col mgr; col pid])) [name; lvl]
  = [["KING"; "1"]; ["JONES"; "2"]; ["BLAKE"; "2"]; ["SCOTT"; "3"]].
Proof. check. Qed.

(** [WHERE ROWNUM <= 2]: two of the rows *)
Example rownum : List.length (run OceanBaseOracle (rownum_le emp 2)) = 2%nat.
Proof. check. Qed.

(** [SELECT * FROM sales PIVOT (SUM (amt) FOR q IN (1 AS q1, 2 AS q2))] *)
Notation region := (Attr_string "region").
Notation q := (Attr_Z "q").
Notation amt := (Attr_Z "amt").
Notation q1 := (Attr_Z "q1").
Notation q2 := (Attr_Z "q2").
Definition sales := values_ [region; q; amt] [[str "N"; int 1; int 10]; [str "N"; int 2; int 20]; [str "S"; int 1; int 5]].
Example pivot_rows :
  rows OceanBaseOracle (pivot sales [region] "sum" (col amt) (col q) [(int 1, q1); (int 2, q2)]) [region; q1; q2]
  = [["N"; "10"; "20"]; ["S"; "5"; "NULL"]].
Proof. check. Qed.

(** [SELECT * FROM t UNPIVOT (v FOR k IN (a AS 'a', b AS 'b'))]: the NULLs are excluded *)
Notation a := (Attr_Z "a").
Notation b := (Attr_Z "b").
Notation k := (Attr_string "k").
Notation v := (Attr_Z "v").
Definition wide := values_ [id; a; b] [[int 1; int 10; cst NullZ]; [int 2; int 20; int 30]].
Example unpivot_rows :
  rows OceanBaseOracle (unpivot wide [id] k v [(a, str "a"); (b, str "b")]) [id; k; v]
  = [["1"; "a"; "10"]; ["2"; "a"; "20"]; ["2"; "b"; "30"]].
Proof. check. Qed.

(** [TO_NUMBER], with a format model whose separators are not part of the number *)
Notation c0 := (Attr_Z "c0").
Definition val (e : sexpr) : string := match rows OceanBaseOracle (select_where [as_ e c0] [] c_true) [c0] with
                                       | [[x]] => x | _ => "?" end.
Example to_number_plain : val (fn "to_number" [str "12.5"]) = "12.5".
Proof. check. Qed.
Example to_number_fmt : val (fn "to_number" [str "$1,234.5"; str "$9,999.9"]) = "1234.5".
Proof. check. Qed.
Example to_number_bad : val (fn "to_number" [str "12a"]) = "ERROR".
Proof. check. Qed.
