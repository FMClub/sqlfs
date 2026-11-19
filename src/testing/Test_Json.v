(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Tests of JSON (TODO 1.6).                                                     *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String ZArith NArith.

Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.

Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax
        Dialects ValueKit PostgreSQL MySQL SQLite OceanBase SpecRunner.

Import Tuple.
Import ListNotations.
Open Scope string_scope.

Ltac check := vm_compute; reflexivity.

Notation c0 := (Attr_string "c0").

Definition run (d : vsem) (q : squery) :=
  eval_query_result ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).

Definition text (d : vsem) (e : sexpr) : string :=
  match run d (select_where [as_ (fn "cast_string" [e]) c0] [] c_true) with
  | QR_Rows _ (t :: nil) => show_value (dot (TD d) t c0)
  | QR_Error _ => "ERROR"
  | _ => "?"
  end.

Definition holds (d : vsem) (c : scond) : bool :=
  match run d (select_where [as_ (int 1) (Attr_Z "c1")] [] c) with QR_Rows _ (_ :: _) => true | _ => false end.

Definition doc := str "{""b"": [10, 20, {""c"": ""x""}], ""a"": 1.50, ""a"": true}".

(** * PostgreSQL *)

(** [jsonb]: keys sorted by length then bytes, the last duplicate kept; [json]: the text as it is *)
Example pg_jsonb : text PostgreSQL (fn "cast_jsonb" [doc]) = "{""a"": true, ""b"": [10, 20, {""c"": ""x""}]}".
Proof. check. Qed.

Example pg_json : text PostgreSQL (fn "cast_json" [doc]) = "{""b"": [10, 20, {""c"": ""x""}], ""a"": 1.50, ""a"": true}".
Proof. check. Qed.

Example pg_arrow : text PostgreSQL (fn "->" [fn "cast_jsonb" [doc]; str "b"]) = "[10, 20, {""c"": ""x""}]".
Proof. check. Qed.

Example pg_arrow_text : text PostgreSQL (fn "->>" [fn "#>" [fn "cast_jsonb" [doc]; str "{b,2}"]; str "c"]) = "x".
Proof. check. Qed.

Example pg_negative_index : text PostgreSQL (fn "->" [fn "->" [fn "cast_jsonb" [doc]; str "b"]; int (-2)]) = "20".
Proof. check. Qed.

Example pg_contains : holds PostgreSQL (pred "@>" [fn "cast_jsonb" [doc]; fn "cast_jsonb" [str "{""b"": [20]}"]]) = true.
Proof. check. Qed.

Example pg_exists : holds PostgreSQL (pred "?" [fn "cast_jsonb" [doc]; str "a"]) = true.
Proof. check. Qed.

Example pg_typeof : text PostgreSQL (fn "jsonb_typeof" [fn "->" [fn "cast_jsonb" [doc]; str "b"]]) = "array".
Proof. check. Qed.

Example pg_build : text PostgreSQL (fn "jsonb_build_object" [str "k"; int 1; str "a"; str "v"]) = "{""a"": ""v"", ""k"": 1}".
Proof. check. Qed.

Example pg_invalid : text PostgreSQL (fn "cast_jsonb" [str "{""a"": }"]) = "ERROR".
Proof. check. Qed.

(** * MySQL *)

Example my_extract : text MySQL (fn "json_extract" [doc; str "$.b[2].c"]) = """x""".
Proof. check. Qed.

Example my_unquote : text MySQL (fn "->>" [doc; str "$.b[2].c"]) = "x".
Proof. check. Qed.

Example my_object : text MySQL (fn "json_object" [str "k"; int 1; str "a"; cst (VD 150 2)]) = "{""a"": 1.50, ""k"": 1}".
Proof. check. Qed.

Example my_type : text MySQL (fn "json_type" [fn "json_extract" [doc; str "$.b"]]) = "ARRAY".
Proof. check. Qed.

Example my_length : text MySQL (fn "json_length" [doc; str "$.b"]) = "3".
Proof. check. Qed.

Example my_contains : text MySQL (fn "json_contains" [doc; str "{""b"": [20]}"]) = "1".
Proof. check. Qed.

Example my_invalid : text MySQL (fn "json_extract" [str "{oops"; str "$.a"]) = "ERROR".
Proof. check. Qed.

(** a JSON string compared with a SQL string *)
Example my_compare_scalar : holds MySQL (pred "=" [fn "json_extract" [doc; str "$.b[2].c"]; str "x"]) = true.
Proof. check. Qed.

(** * SQLite: texts and SQL values *)

Example lite_json : text SQLite (fn "json" [str " { ""a"" : [1, 2] } "]) = "{""a"":[1,2]}".
Proof. check. Qed.

Example lite_extract : text SQLite (fn "json_extract" [doc; str "$.b[2].c"]) = "x".
Proof. check. Qed.

Example lite_arrow : text SQLite (fn "->" [doc; str "$.b"]) = "[10,20,{""c"":""x""}]".
Proof. check. Qed.

Example lite_last : text SQLite (fn "json_extract" [doc; str "$.b[#-1].c"]) = "x".
Proof. check. Qed.

Example lite_type : text SQLite (fn "json_type" [doc; str "$.b[0]"]) = "integer".
Proof. check. Qed.

Example lite_array : text SQLite (fn "json_array" [int 1; str "two"; cst NullZ]) = "[1,""two"",null]".
Proof. check. Qed.
