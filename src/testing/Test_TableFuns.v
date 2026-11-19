(** * Table functions (TODO 3.4) *)
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
Notation g := (Attr_Z "g").
Notation h := (Attr_Z "h").
Notation x := (Attr_Z "x").
Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).
Definition rows (d : vsem) (q : squery) (n : nat) : list (list string) :=
  map (fun t => map (fun i => show_value (dot (TD d) t (out_attr i))) (seq 0 n)) (run d q).
Definition accepts (d : vsem) (q : squery) : bool := accepted_by (dialect_of d) (to_dialect d q).
Definition s (t : string) := str t.
Definition tf (d : vsem) (name : string) (args : list sexpr) (ord : bool) (n : nat) : list (list string) :=
  let atts := firstn n [g; h; x] in
  rows d (select_where (map (fun p => as_ (col (fst p)) (Attr_Z ("c" ++ NullValues.string_of_Z (Z.of_nat (snd p))))) (combine atts (seq 0 n))) [from_fun name args ord atts] c_true) n.

(** [generate_series] (PostgreSQL manual 9.25) *)
Example gs_int : tf PostgreSQL "generate_series" [int 2; int 4] false 1 = [["2"]; ["3"]; ["4"]].
Proof. check. Qed.
Example gs_step : tf PostgreSQL "generate_series" [int 5; int 1; int (-2)] false 1 = [["5"]; ["3"]; ["1"]].
Proof. check. Qed.
Example gs_empty : tf PostgreSQL "generate_series" [int 4; int 3] false 1 = [].
Proof. check. Qed.
Example gs_numeric : tf PostgreSQL "generate_series" [cst (VD 11 1); int 4; int 1] false 1 = [["1.1"]; ["2.1"]; ["3.1"]].
Proof. check. Qed.
Example gs_ts : List.length (tf PostgreSQL "generate_series"
                     [fn "cast_timestamp" [s "2008-03-01 00:00"]; fn "cast_timestamp" [s "2008-03-04 12:00"];
                      fn "cast_interval" [s "10 hours"]] false 1) = 9%nat.
Proof. check. Qed.
Example gs_ord : tf PostgreSQL "generate_series" [int 10; int 12] true 2 = [["10"; "1"]; ["11"; "2"]; ["12"; "3"]].
Proof. check. Qed.

(** [unnest] *)
Definition arr (l : list sexpr) := fn "array" l.
Example unnest2 : tf PostgreSQL "unnest" [arr [int 1; int 2]; arr [s "foo"; s "bar"; s "baz"]] false 2
  = [["1"; "foo"]; ["2"; "bar"]; ["NULL"; "baz"]].
Proof. check. Qed.

(** JSON *)
Definition jb (t : string) := fn "cast_jsonb" [s t].
Example ja_elements : tf PostgreSQL "jsonb_array_elements" [jb "[1,true, [2,false]]"] false 1 = [["1"]; ["true"]; ["[2, false]"]].
Proof. check. Qed.
Example j_each_text : tf PostgreSQL "jsonb_each_text" [jb "{""a"":""foo"", ""b"":""bar""}"] false 2 = [["a"; "foo"]; ["b"; "bar"]].
Proof. check. Qed.
Example j_keys : tf PostgreSQL "jsonb_object_keys" [jb "{""f1"":""abc"",""f2"":{""f3"":""a""}}"] false 1 = [["f1"]; ["f2"]].
Proof. check. Qed.

(** text *)
Example s2t : tf PostgreSQL "string_to_table" [s "xx~^~yy~^~zz"; s "~^~"; s "yy"] false 1 = [["xx"]; ["NULL"]; ["zz"]].
Proof. check. Qed.
Example rsplit : tf PostgreSQL "regexp_split_to_table" [s "hello world"; s "\s+"] false 1 = [["hello"]; ["world"]].
Proof. check. Qed.

(** a lateral call: [SELECT t.c0, g FROM (VALUES (2), (3)) t, generate_series (1, t.c0) g] *)
Example gs_lateral :
  rows PostgreSQL (select_where [as_ (col c1) c0; as_ (col g) c1]
                     [join_lateral J_Inner (from_as (values_ [c0] [[int 2]; [int 3]]) [(c0, c1)])
                                   (from_fun "generate_series" [int 1; col c1] false [g]) c_true] c_true) 2
  = [["2"; "1"]; ["2"; "2"]; ["3"; "1"]; ["3"; "2"]; ["3"; "3"]].
Proof. check. Qed.

(** MySQL [JSON_TABLE (doc, '$[*]' COLUMNS (x PATH '$.x', y PATH '$.y'))] *)
Example json_table_rows :
  tf MySQL "json_table" [s "[{""x"":2,""y"":""8""},{""x"":""3"",""y"":""7""},{""y"":6}]"; s "$[*]"; s "$.x"; s "$.y"] false 2
  = [["2"; "8"]; ["3"; "7"]; ["NULL"; "6"]].
Proof. check. Qed.
(** SQLite [json_each]: [key], [value], [type] *)
Example lite_each : tf SQLite "json_each" [s "[10,""a""]"] false 3 = [["0"; "10"; "integer"]; ["1"; "a"; "text"]].
Proof. check. Qed.
(** an unknown table function is rejected *)
Example unknown_tf : accepts MySQL (select_where [as_ (col g) c0] [from_fun "generate_series" [int 1; int 2] false [g]] c_true) = false.
Proof. check. Qed.
