(** * JSON functions (TODO 2.8)

    The functions of the C library ([sqrt], [exp], [ln], [sin], ...) are correctly rounded; the
    [numeric] versions of PostgreSQL have the scale of [numeric.c]. The expected texts are the ones of
    the engines. *)
Require Import List String ZArith NArith.

Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.

Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax
        Dialects ValueKit PostgreSQL MySQL SQLite OceanBase SpecRunner.

Import Tuple.
Import ListNotations.
Open Scope string_scope.

Ltac check := vm_compute; reflexivity.

Notation c0 := (Attr_Z "c0").

Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).

Definition text (d : vsem) (e : sexpr) : string :=
  match run d (select_where [as_ (fn "cast_string" [e]) c0] [] c_true) with
  | t :: nil => show_value (dot (TD d) t (out_attr 0))
  | _ => "?"
  end.

Definition fails (d : vsem) (e : sexpr) : bool :=
  match eval_query_result ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) 
                          (to_dialect d (select_where [as_ e c0] [] c_true)) with
  | QR_Error _ => true
  | _ => false
  end.

Definition dbl (n : Z) := cst (VFl false n 0).
Definition s (x : string) := str x.
Definition jb (x : string) := fn "cast_jsonb" [str x].
Definition holds (d : vsem) (c : scond) : bool :=
  match run d (select_where [as_ (int 1) c0] [] c) with nil => false | _ => true end.

(** MySQL (manual 14.17) *)
Example jf_1 : text MySQL (fn "json_set" [s "{""a"": 1, ""b"": [2, 3]}"; s "$.a"; int 10; s "$.c"; s "[true, false]"]) = "{""a"": 10, ""b"": [2, 3], ""c"": ""[true, false]""}".
Proof. check. Qed.

Example jf_2 : text MySQL (fn "json_insert" [s "{""a"": 1, ""b"": [2, 3]}"; s "$.a"; int 10; s "$.c"; s "[true, false]"]) = "{""a"": 1, ""b"": [2, 3], ""c"": ""[true, false]""}".
Proof. check. Qed.

Example jf_3 : text MySQL (fn "json_replace" [s "{""a"": 1, ""b"": [2, 3]}"; s "$.a"; int 10; s "$.c"; s "[true, false]"]) = "{""a"": 10, ""b"": [2, 3]}".
Proof. check. Qed.

Example jf_4 : text MySQL (fn "json_remove" [s "[""a"", [""b"", ""c""], ""d""]"; s "$[1]"]) = "[""a"", ""d""]".
Proof. check. Qed.

Example jf_5 : text MySQL (fn "json_array_append" [s "[""a"", [""b"", ""c""], ""d""]"; s "$[1]"; int 1]) = "[""a"", [""b"", ""c"", 1], ""d""]".
Proof. check. Qed.

Example jf_6 : text MySQL (fn "json_array_append" [s "{""a"": 1}"; s "$"; s "z"]) = "[{""a"": 1}, ""z""]".
Proof. check. Qed.

Example jf_7 : text MySQL (fn "json_array_insert" [s "[""a"", {""b"": [1, 2]}, [3, 4]]"; s "$[1]"; s "x"]) = "[""a"", ""x"", {""b"": [1, 2]}, [3, 4]]".
Proof. check. Qed.

Example jf_8 : text MySQL (fn "json_merge_patch" [s "{""a"":1, ""b"":2}"; s "{""a"":3, ""c"":4}"]) = "{""a"": 3, ""b"": 2, ""c"": 4}".
Proof. check. Qed.

Example jf_9 : text MySQL (fn "json_merge_patch" [s "{""a"":1, ""b"":2}"; s "{""b"":null}"]) = "{""a"": 1}".
Proof. check. Qed.

Example jf_10 : text MySQL (fn "json_merge_preserve" [s "[1, 2]"; s "[true, false]"]) = "[1, 2, true, false]".
Proof. check. Qed.

Example jf_11 : text MySQL (fn "json_merge_preserve" [s "{""a"": 1, ""b"": 2}"; s "{""a"": 3, ""c"": 4}"]) = "{""a"": [1, 3], ""b"": 2, ""c"": 4}".
Proof. check. Qed.

Example jf_12 : text MySQL (fn "json_depth" [s "[10, {""a"": 20}]"]) = "3".
Proof. check. Qed.

Example jf_13 : text MySQL (fn "json_contains_path" [s "{""a"": 1, ""b"": 2, ""c"": {""d"": 4}}"; s "one"; s "$.a"; s "$.e"]) = "1".
Proof. check. Qed.

Example jf_14 : text MySQL (fn "json_contains_path" [s "{""a"": 1, ""b"": 2, ""c"": {""d"": 4}}"; s "all"; s "$.a"; s "$.e"]) = "0".
Proof. check. Qed.

Example jf_15 : text MySQL (fn "json_search" [s "[""abc"", [{""k"": ""10""}, ""def""], {""x"":""abc""}, {""y"":""bcd""}]"; s "one"; s "abc"]) = """$[0]""".
Proof. check. Qed.

Example jf_16 : text MySQL (fn "json_search" [s "[""abc"", [{""k"": ""10""}, ""def""], {""x"":""abc""}, {""y"":""bcd""}]"; s "all"; s "abc"]) = "[""$[0]"", ""$[2].x""]".
Proof. check. Qed.

Example jf_17 : text MySQL (fn "json_overlaps" [s "[1,3,5,7]"; s "[2,5,7]"]) = "1".
Proof. check. Qed.


(** SQLite (json1) *)
Example jf_18 : text SQLite (fn "json_set" [s "{""a"":2,""c"":4}"; s "$.a"; int 99]) = "{""a"":99,""c"":4}".
Proof. check. Qed.

Example jf_19 : text SQLite (fn "json_insert" [s "{""a"":2,""c"":4}"; s "$.e"; int 99]) = "{""a"":2,""c"":4,""e"":99}".
Proof. check. Qed.

Example jf_20 : text SQLite (fn "json_replace" [s "{""a"":2,""c"":4}"; s "$.a"; int 99]) = "{""a"":99,""c"":4}".
Proof. check. Qed.

Example jf_21 : text SQLite (fn "json_remove" [s "[0,1,2,3,4]"; s "$[2]"]) = "[0,1,3,4]".
Proof. check. Qed.

Example jf_22 : text SQLite (fn "json_patch" [s "{""a"":1,""b"":2}"; s "{""c"":3,""d"":4}"]) = "{""a"":1,""b"":2,""c"":3,""d"":4}".
Proof. check. Qed.

Example jf_23 : text SQLite (fn "json_quote" [s "verdant"]) = """verdant""".
Proof. check. Qed.


(** PostgreSQL (manual 9.16) *)
Example jf_24 : text PostgreSQL (fn "jsonb_set" [jb "[{""f1"":1,""f2"":null},2,null,3]"; s "{0,f1}"; jb "[2,3,4]"; cst (Value_bool (Some false))]) = "[{""f1"": [2, 3, 4], ""f2"": null}, 2, null, 3]".
Proof. check. Qed.

Example jf_25 : text PostgreSQL (fn "jsonb_set" [jb "[{""f1"":1,""f2"":null},2]"; s "{0,f3}"; jb "[2,3,4]"]) = "[{""f1"": 1, ""f2"": null, ""f3"": [2, 3, 4]}, 2]".
Proof. check. Qed.

Example jf_26 : text PostgreSQL (fn "jsonb_insert" [jb "{""a"": [0,1,2]}"; s "{a,1}"; jb """new_value"""]) = "{""a"": [0, ""new_value"", 1, 2]}".
Proof. check. Qed.

Example jf_27 : text PostgreSQL (fn "jsonb_insert" [jb "{""a"": [0,1,2]}"; s "{a,1}"; jb """new_value"""; cst (Value_bool (Some true))]) = "{""a"": [0, 1, ""new_value"", 2]}".
Proof. check. Qed.

(** [json_strip_nulls] of a string literal, and its second argument (the [null] elements of the arrays too) *)
Example jf_27a : text PostgreSQL (fn "json_strip_nulls" [str "{""a"":1,""b"":null,""c"":[2,null,3],""d"":{""e"":4,""f"":null}}"]) =
  "{""a"":1,""c"":[2,null,3],""d"":{""e"":4}}".
Proof. check. Qed.
Example jf_27b : text PostgreSQL (fn "json_strip_nulls" [str "{""a"":1,""b"":null,""c"":[2,null,3],""d"":{""e"":4,""f"":null}}"; cst (NullValues.Value_bool (Some true))]) =
  "{""a"":1,""c"":[2,3],""d"":{""e"":4}}".
Proof. check. Qed.

Example jf_28 : text PostgreSQL (fn "jsonb_strip_nulls" [jb "[{""f1"":1, ""f2"":null}, 2, null, 3]"]) = "[{""f1"": 1}, 2, null, 3]".
Proof. check. Qed.

Example jf_29 : text PostgreSQL (fn "#-" [jb "{""a"": {""b"":[""c"", ""d""]}}"; s "{a,b,1}"]) = "{""a"": {""b"": [""c""]}}".
Proof. check. Qed.

Example jf_30 : text PostgreSQL (fn "||" [jb "[""a"", ""b""]"; jb "[""a"", ""d""]"]) = "[""a"", ""b"", ""a"", ""d""]".
Proof. check. Qed.

Example jf_31 : text PostgreSQL (fn "||" [jb "{""a"": ""b""}"; jb "{""c"": ""d""}"]) = "{""a"": ""b"", ""c"": ""d""}".
Proof. check. Qed.

Example jf_32 : text PostgreSQL (fn "-" [jb "{""a"": ""b"", ""c"": ""d""}"; s "a"]) = "{""c"": ""d""}".
Proof. check. Qed.

Example jf_33 : text PostgreSQL (fn "-" [jb "[""a"", ""b""]"; int 1]) = "[""a""]".
Proof. check. Qed.

Example jf_34 : text PostgreSQL (fn "||" [s "ab"; s "cd"]) = "abcd".
Proof. check. Qed.

Example jf_35 : text PostgreSQL (fn "-" [int 5; int 2]) = "3".
Proof. check. Qed.

Example jf_36 : holds PostgreSQL (pred "?|" [jb "{""a"":1, ""b"":2, ""c"":3}"; s "{b,d}"]) = true.
Proof. check. Qed.

Example jf_37 : holds PostgreSQL (pred "?&" [jb "{""a"":1, ""b"":2, ""c"":3}"; s "{a,d}"]) = false.
Proof. check. Qed.

Example jf_38 : text MySQL (fn "json_pretty" [s "[1,3,5]"]) = "[
  1,
  3,
  5
]".
Proof. check. Qed.

Example jf_39 : text PostgreSQL (fn "jsonb_pretty" [jb "[{""f1"":1,""f2"":null},2]"]) = "[
    {
        ""f1"": 1,
        ""f2"": null
    },
    2
]".
Proof. check. Qed.


(** PostgreSQL arrays (manual 9.19) *)
Definition arr (l : list sexpr) := fn "array" l.
Example arr_101 : text PostgreSQL (fn "array_append" [arr [int 1; int 2]; int 3]) = "{1,2,3}".
Proof. check. Qed.

Example arr_102 : text PostgreSQL (fn "array_cat" [arr [int 1; int 2; int 3]; arr [int 4; int 5]]) = "{1,2,3,4,5}".
Proof. check. Qed.

Example arr_103 : text PostgreSQL (fn "array_length" [arr [int 1; int 2; int 3]; int 1]) = "3".
Proof. check. Qed.

Example arr_104 : text PostgreSQL (fn "cardinality" [arr [int 1; int 2; int 3]]) = "3".
Proof. check. Qed.

Example arr_105 : text PostgreSQL (fn "array_position" [arr [s "sun"; s "mon"; s "tue"]; s "mon"]) = "2".
Proof. check. Qed.

Example arr_106 : text PostgreSQL (fn "array_positions" [arr [s "A"; s "A"; s "B"; s "A"]; s "A"]) = "{1,2,4}".
Proof. check. Qed.

Example arr_107 : text PostgreSQL (fn "array_remove" [arr [int 1; int 2; int 3; int 2]; int 2]) = "{1,3}".
Proof. check. Qed.

Example arr_108 : text PostgreSQL (fn "array_replace" [arr [int 1; int 2; int 5; int 4]; int 5; int 3]) = "{1,2,3,4}".
Proof. check. Qed.

Example arr_109 : text PostgreSQL (fn "array_to_string" [arr [int 1; int 2; int 3; cst NullZ; int 5]; s ","; s "*"]) = "1,2,3,*,5".
Proof. check. Qed.

Example arr_110 : text PostgreSQL (fn "string_to_array" [s "xx~~yy~~zz"; s "~~"; s "yy"]) = "{xx,NULL,zz}".
Proof. check. Qed.

Example arr_111 : text PostgreSQL (fn "array_dims" [arr [int 1; int 2; int 3]]) = "[1:3]".
Proof. check. Qed.

Example arr_112 : text PostgreSQL (arr [s "a b"; s "c"; cst NullZ]) = "{""a b"",c,NULL}".
Proof. check. Qed.

Example arr_113 : text PostgreSQL (fn "subscript" [arr [int 10; int 20; int 30]; int 2]) = "20".
Proof. check. Qed.

Example arr_114 : text PostgreSQL (fn "slice" [arr [int 10; int 20; int 30]; int 2; int 3]) = "{20,30}".
Proof. check. Qed.

Example arr_115 : text PostgreSQL (fn "||" [arr [int 1; int 2]; arr [int 3; int 4]]) = "{1,2,3,4}".
Proof. check. Qed.

Example arr_116 : text PostgreSQL (fn "||" [arr [int 1; int 2]; int 3]) = "{1,2,3}".
Proof. check. Qed.

Example arr_117 : holds PostgreSQL (pred "@>" [arr [int 1; int 4; int 3]; arr [int 3; int 1; int 3]]) = true.
Proof. check. Qed.

Example arr_118 : holds PostgreSQL (pred "&&" [arr [int 1; int 4; int 3]; arr [int 2; int 1]]) = true.
Proof. check. Qed.

Example arr_119 : holds PostgreSQL (pred "=" [arr [int 1; int 2; int 3]; arr [int 1; int 2; int 3]]) = true.
Proof. check. Qed.

Example arr_120 : holds PostgreSQL (pred "<" [arr [int 1; int 2; int 3]; arr [int 1; int 2; int 4]]) = true.
Proof. check. Qed.

Example arr_121 : holds PostgreSQL (pred "=any" [int 3; arr [int 1; int 2; int 3]]) = true.
Proof. check. Qed.

Example arr_122 : holds PostgreSQL (pred "<all" [int 3; arr [int 1; int 2; int 3]]) = false.
Proof. check. Qed.

