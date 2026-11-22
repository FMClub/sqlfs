(** * Functions added by the dialect closeouts (TODO 4.1-4.8) *)
Require Import List String ZArith NArith.
Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.
Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax
        Dialects PostgreSQL MySQL SQLite OceanBase MariaDB TiDB SpecRunner.
Import Tuple.
Import ListNotations.
Open Scope string_scope.
Ltac check := vm_compute; reflexivity.
Notation c0 := (Attr_Z "c0").
Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).
Definition val (d : vsem) (e : sexpr) : string :=
  match run d (select_where [as_ e c0] [] c_true) with
  | t :: nil => show_value (dot (TD d) t c0)
  | _ => "?"
  end.

(** ** PostgreSQL (4.1) *)
Example pg_scale : val PostgreSQL (fn "scale" [cst (VD 12340 3)]) = "3".
Proof. check. Qed.
Example pg_min_scale : val PostgreSQL (fn "min_scale" [cst (VD 12340 3)]) = "2".
Proof. check. Qed.
Example pg_trim_scale : val PostgreSQL (fn "trim_scale" [cst (VD 12340 3)]) = "12.34".
Proof. check. Qed.
Example pg_to_bin : val PostgreSQL (fn "to_bin" [int 10]) = "1010".
Proof. check. Qed.
Example pg_to_oct : val PostgreSQL (fn "to_oct" [int (-1)]) = "37777777777".
Proof. check. Qed.
Example pg_char_alias : val PostgreSQL (fn "character_length" [str "abc"]) = "3".
Proof. check. Qed.

(** ** The MySQL family (4.2-4.6, 4.8): the examples of the MySQL 8.4 manual *)
Example my_conv1 : val MySQL (fn "conv" [str "a"; int 16; int 2]) = "1010".
Proof. check. Qed.
Example my_conv2 : val MySQL (fn "conv" [str "6E"; int 18; int 8]) = "172".
Proof. check. Qed.
Example my_conv3 : val MySQL (fn "conv" [int (-17); int 10; int (-18)]) = "-H".
Proof. check. Qed.
Example my_bin : (val MySQL (fn "bin" [int 12]), val MySQL (fn "oct" [int 12])) = ("1100", "14").
Proof. check. Qed.
Example my_crc32 : val MySQL (fn "crc32" [str "MySQL"]) = "3259397556".
Proof. check. Qed.
Example my_inet_aton : (val MySQL (fn "inet_aton" [str "10.0.5.9"]), val MySQL (fn "inet_aton" [str "127.1"]))
                       = ("167773449", "2130706433").
Proof. check. Qed.
Example my_inet_ntoa : val MySQL (fn "inet_ntoa" [int 167773449]) = "10.0.5.9".
Proof. check. Qed.
Example my_quote : val MySQL (fn "quote" [str "Don't!"]) = "'Don\'t!'".
Proof. check. Qed.
Example my_make_set : val MySQL (fn "make_set" [int 5; str "hello"; str "nice"; str "world"]) = "hello,world".
Proof. check. Qed.
Example my_export_set : val MySQL (fn "export_set" [int 5; str "Y"; str "N"; str ","; int 4]) = "Y,N,Y,N".
Proof. check. Qed.
Example my_lcase : (val MySQL (fn "lcase" [str "ABC"]), val TiDB (fn "ucase" [str "abc"])) = ("abc", "ABC").
Proof. check. Qed.
Example my_weekofyear : val MySQL (fn "weekofyear" [str "2008-02-20"]) = "8".
Proof. check. Qed.

(** ** PostgreSQL behaviours found by its regression tests (TODO 5.3) *)
(** [text || anynonarray] converts the other operand: ['four: ' || 2 + 2] *)
Example pg_concat_int : val PostgreSQL (fn "||" [str "four: "; fn "+" [int 2; int 2]]) = "four: 4".
Proof. check. Qed.
(** a boolean is [t] or [f] in [concat] (its output function) *)
Example pg_concat_bool : val PostgreSQL (fn "concat" [str "x"; cst (NullValues.Value_bool (Some true))]) = "xt".
Proof. check. Qed.
(** a date compared with a string literal: the literal is read as a date *)
Example pg_date_literal : val PostgreSQL (e_case (pred "<" [fn "cast_date" [str "1999-01-08"]; str "2000-01-01"]) (int 1) (int 0)) = "1".
Proof. check. Qed.
(** a timestamp is printed with the fewest fractional digits *)
Example pg_ts_text : val PostgreSQL (fn "date_trunc" [str "week"; fn "cast_timestamp" [str "2004-02-29 15:44:17.71393"]]) = "2004-02-23 00:00:00".
Proof. check. Qed.
(** [json] keeps its text *)
Example pg_json_text : val PostgreSQL (fn "cast_json" [str "[1,2]"]) = "[1,2]".
Proof. check. Qed.
(** [numeric] modulo, and the cast of a [numeric] to an integer (rounded, then checked) *)
Example pg_num_mod : val PostgreSQL (fn "%" [cst (VD 700 1); int 70]) = "0.0".
Proof. check. Qed.
Example pg_num_mod_big : val PostgreSQL (fn "mod" [cst (VD 999999999999999999999 0); cst (VD 1000000000000000000000 0)]) = "999999999999999999999".
Proof. check. Qed.
Example pg_num_to_int : val PostgreSQL (fn "cast_int" [cst (VD (-21474836484) 1)]) = "-2147483648".
Proof. check. Qed.
(** a string of digits is read as a date in the MySQL family ([str_to_datetime]; MariaDB [group_by.result]) *)
Example my_date_digits : val MariaDB (fn "date" [str "20050606"]) = "2005-06-06".
Proof. check. Qed.
(** a string with an exponent, read as a number ([ROUND ('123e-2')] is 1) *)
Example my_exp_string : val MySQL (fn "round" [str "123e-2"]) = "1".
Proof. check. Qed.
(** leading inline flags of a regular expression ([(?i)]: MySQL [regular_expressions_func.result]) *)
Example my_rx_inline : val MySQL (e_case (pred "regexp" [str "ABC"; str "(?i)^abc$"]) (int 1) (int 0)) = "1".
Proof. check. Qed.
(** scoped inline flags ([(?i:a)b]: the [a] in either case, the [b] in lower case) *)
Example my_rx_scoped : (val MySQL (e_case (pred "regexp" [str "Ab"; str "(?i:a)b"]) (int 1) (int 0)),
                        val MySQL (e_case (pred "regexp" [str "Ab"; str "((?i)a)(?-i)b"]) (int 1) (int 0)),
                        val MySQL (e_case (pred "regexp" [str "aB"; str "((?i)a)(?-i)b"]) (int 1) (int 0)),
                        (* PostgreSQL has the embedded options at the start of the expression only
                           ([regc_lex.c]: REG_BADRPT) *)
                        val PostgreSQL (e_case (pred "~" [str "Ab"; str "((?i)a)b"]) (int 1) (int 0)))
                       = ("1", "1", "0", "ERROR").
Proof. check. Qed.
(** composite interval units: [INTERVAL 1 DAY_HOUR] is one hour, ['1 2'] one day and two hours *)
Example my_interval_day_hour :
  (val MySQL (fn "date_add" [str "2010-11-11"; fn "interval" [int 1; str "DAY_HOUR"]]),
   val MySQL (fn "date_add" [str "2010-11-11"; fn "interval" [str "1 2"; str "DAY_HOUR"]])) = ("2010-11-11 01:00:00", "2010-11-12 02:00:00").
Proof. check. Qed.
