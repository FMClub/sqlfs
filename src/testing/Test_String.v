(** * String functions (TODO 2.2)

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

Example str_1 : text PostgreSQL (fn "lpad" [s "hi"; int 5; s "xy"]) = "xyxhi".
Proof. check. Qed.

Example str_2 : text PostgreSQL (fn "lpad" [s "hello"; int 3]) = "hel".
Proof. check. Qed.

Example str_3 : text MySQL (fn "lpad" [s "hi"; int 5; s ""]) = "NULL".
Proof. check. Qed.

Example str_4 : text MySQL (fn "rpad" [s "hi"; int 5; s "?"]) = "hi???".
Proof. check. Qed.

Example str_5 : text MySQL (fn "substring_index" [s "www.mysql.com"; s "."; int 2]) = "www.mysql".
Proof. check. Qed.

Example str_6 : text MySQL (fn "substring_index" [s "www.mysql.com"; s "."; int (-2)]) = "mysql.com".
Proof. check. Qed.

Example str_7 : text PostgreSQL (fn "split_part" [s "abc~@~def~@~ghi"; s "~@~"; int 2]) = "def".
Proof. check. Qed.

Example str_8 : text PostgreSQL (fn "split_part" [s "abc,def,ghi"; s ","; int (-1)]) = "ghi".
Proof. check. Qed.

Example str_9 : text PostgreSQL (fn "translate" [s "12345"; s "143"; s "ax"]) = "a2x5".
Proof. check. Qed.

Example str_10 : text PostgreSQL (fn "initcap" [s "hi THOMAS"]) = "Hi Thomas".
Proof. check. Qed.

Example str_11 : text PostgreSQL (fn "overlay" [s "Txxxxas"; s "hom"; int 2; int 4]) = "Thomas".
Proof. check. Qed.

Example str_12 : text PostgreSQL (fn "position" [s "om"; s "Thomas"]) = "3".
Proof. check. Qed.

Example str_13 : text PostgreSQL (fn "btrim" [s "xyxtrimyyx"; s "xyz"]) = "trim".
Proof. check. Qed.

Example str_14 : text MySQL (fn "trim_leading" [s "xxxbarxxx"; s "x"]) = "barxxx".
Proof. check. Qed.

Example str_15 : text MySQL (fn "trim_both" [s "xyxbarxyx"; s "xy"]) = "xbarxyx".
Proof. check. Qed.

Example str_16 : text PostgreSQL (fn "concat_ws" [s ","; s "abcde"; int 2; cst NullZ; int 22]) = "abcde,2,22".
Proof. check. Qed.

Example str_17 : text PostgreSQL (fn "md5" [s "abc"]) = "900150983cd24fb0d6963f7d28e17f72".
Proof. check. Qed.

Example str_18 : text MySQL (fn "sha1" [s "abc"]) = "a9993e364706816aba3e25717850c26c9cd0d89d".
Proof. check. Qed.

Example str_19 : text MySQL (fn "sha2" [s "abc"; int 224]) = "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7".
Proof. check. Qed.

Example str_20 : text PostgreSQL (fn "quote_literal" [s "O'Reilly"]) = "'O''Reilly'".
Proof. check. Qed.

Example str_21 : text PostgreSQL (fn "quote_ident" [s "Foo bar"]) = """Foo bar""".
Proof. check. Qed.

Example str_22 : text PostgreSQL (fn "quote_ident" [s "select"]) = """select""".
Proof. check. Qed.

Example str_23 : text PostgreSQL (fn "format" [s "Hello %s, %1$s"; s "World"]) = "Hello World, World".
Proof. check. Qed.

Example str_24 : text PostgreSQL (fn "format" [s "INSERT INTO %I VALUES(%L)"; s "Foo bar"; s "O'Reilly"]) = "INSERT INTO ""Foo bar"" VALUES('O''Reilly')".
Proof. check. Qed.

Example str_25 : text PostgreSQL (fn "ascii" [s "x"]) = "120".
Proof. check. Qed.

Example str_26 : text PostgreSQL (fn "chr" [int 65]) = "A".
Proof. check. Qed.

Example str_27 : fails PostgreSQL (fn "chr" [int 0]) = true.
Proof. check. Qed.

Example str_28 : text PostgreSQL (fn "to_hex" [int 2147483647]) = "7fffffff".
Proof. check. Qed.

Example str_29 : text PostgreSQL (fn "to_hex" [int (-1)]) = "ffffffff".
Proof. check. Qed.

Example str_30 : text MySQL (fn "hex" [int 255]) = "FF".
Proof. check. Qed.

Example str_31 : text MySQL (fn "hex" [s "abc"]) = "616263".
Proof. check. Qed.

Example str_32 : text MySQL (fn "unhex" [s "4D7953514C"]) = "MySQL".
Proof. check. Qed.

Example str_33 : text MySQL (fn "to_base64" [s "abc"]) = "YWJj".
Proof. check. Qed.

Example str_34 : text MySQL (fn "from_base64" [s "YWJj"]) = "abc".
Proof. check. Qed.

Example str_35 : text MySQL (fn "soundex" [s "Hello"]) = "H400".
Proof. check. Qed.

Example str_36 : text MySQL (fn "soundex" [s "Quadratically"]) = "Q36324".
Proof. check. Qed.

Example str_37 : text MySQL (fn "insert" [s "Quadratic"; int 3; int 4; s "What"]) = "QuWhattic".
Proof. check. Qed.

Example str_38 : text MySQL (fn "insert" [s "Quadratic"; int (-1); int 4; s "What"]) = "Quadratic".
Proof. check. Qed.

Example str_39 : text MySQL (fn "elt" [int 1; s "Aa"; s "Bb"]) = "Aa".
Proof. check. Qed.

Example str_40 : text MySQL (fn "field" [s "Bb"; s "Aa"; s "Bb"; s "Cc"]) = "2".
Proof. check. Qed.

Example str_41 : text MySQL (fn "find_in_set" [s "b"; s "a,b,c,d"]) = "2".
Proof. check. Qed.

Example str_42 : text MySQL (fn "format" [cst (VD 123456789 4); int 2]) = "12,345.68".
Proof. check. Qed.

Example str_43 : text MySQL (fn "format" [int 12332; int 0]) = "12,332".
Proof. check. Qed.

Example str_44 : text MySQL (fn "ascii" [s "2"]) = "50".
Proof. check. Qed.

Example str_45 : text MySQL (fn "ord" [s "2"]) = "50".
Proof. check. Qed.

Example str_46 : text MySQL (fn "char" [int 77; int 121; int 83; int 81; int 76]) = "MySQL".
Proof. check. Qed.

Example str_47 : text MySQL (fn "space" [int 3]) = "   ".
Proof. check. Qed.

Example str_48 : text MySQL (fn "strcmp" [s "text"; s "text2"]) = "-1".
Proof. check. Qed.

Example str_49 : text SQLite (fn "hex" [int 12]) = "3132".
Proof. check. Qed.

Example str_50 : text SQLite (fn "quote" [s "it's"]) = "'it''s'".
Proof. check. Qed.

Example str_51 : text SQLite (fn "unicode" [s "A"]) = "65".
Proof. check. Qed.

Example str_52 : text SQLite (fn "char" [int 72; int 105]) = "Hi".
Proof. check. Qed.

Example str_53 : text SQLite (fn "trim" [s "xxhixx"; s "x"]) = "hi".
Proof. check. Qed.

Example str_54 : text SQLite (fn "instr" [s "héllo"; s "l"]) = "3".
Proof. check. Qed.

Example str_55 : text SQLite (fn "length" [s "héllo"]) = "5".
Proof. check. Qed.

Example str_56 : text OceanBaseOracle (fn "lpad" [s "Page 1"; int 15; s "*."]) = "*.*.*.*.*Page 1".
Proof. check. Qed.

Example str_57 : text OceanBaseOracle (fn "translate" [s "SQL*Plus User's Guide"; s " */'"; s "___"]) = "SQL_Plus_Users_Guide".
Proof. check. Qed.

Example str_58 : text OceanBaseOracle (fn "initcap" [s "the soap"]) = "The Soap".
Proof. check. Qed.

Example str_59 : text OceanBaseOracle (fn "ltrim" [s "<=====>BROWNING<=====>"; s "<>="]) = "BROWNING<=====>".
Proof. check. Qed.


(** [LIKE ... ESCAPE], [ILIKE] *)
Definition holds (d : vsem) (c : scond) : bool :=
  match run d (select_where [as_ (int 1) c0] [] c) with nil => false | _ => true end.

Example pg_like_esc : holds PostgreSQL (pred "like_escape" [s "10%"; s "10!%"; s "!"]) = true.
Proof. check. Qed.
Example pg_like_esc_no : holds PostgreSQL (pred "like_escape" [s "100"; s "10!%"; s "!"]) = false.
Proof. check. Qed.
Example pg_ilike : holds PostgreSQL (pred "ilike" [s "ABC"; s "a%"]) = true.
Proof. check. Qed.
Example pg_like_case : holds PostgreSQL (pred "like" [s "ABC"; s "a%"]) = false.
Proof. check. Qed.
Example my_like_esc : holds MySQL (pred "like_escape" [s "a_b"; s "a|_b"; s "|"]) = true.
Proof. check. Qed.
Example lite_like_esc : holds SQLite (pred "like_escape" [s "A%B"; s "a\%b"; s "\"]) = true.
Proof. check. Qed.
Example lite_bad_escape : fails SQLite (e_cond (pred "like_escape" [s "a"; s "a"; s "ab"])) = true.
Proof. check. Qed.
(** MySQL: [ESCAPE NULL] is the default escape [\] (OceanBase [select_basic]) *)
Example my_like_esc_null : holds MySQL (pred "like_escape" [s "David_"; s "David|_"; cst NullZ]) = false.
Proof. check. Qed.
Example my_like_esc_null_hit : holds MySQL (pred "like_escape" [s "David_"; s "David\_"; cst NullZ]) = true.
Proof. check. Qed.
