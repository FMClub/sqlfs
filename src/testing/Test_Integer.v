(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Tests of the integer types and of their overflow (TODO 1.2.3).                *)
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

Notation c0 := (Attr_Z "c0").

Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).

Definition fails (d : vsem) (e : sexpr) : bool :=
  match eval_query_result ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) 
                          (to_dialect d (select_where [as_ e c0] [] c_true)) with
  | QR_Error _ => true
  | _ => false
  end.

Definition text (d : vsem) (e : sexpr) : string :=
  match run d (select_where [as_ e c0] [] c_true) with
  | t :: nil => show_value (dot (TD d) t (out_attr 0))
  | _ => "?"
  end.

Definition int_max := int 2147483647.
Definition big_max := int 9223372036854775807.

(** PostgreSQL: [2147483647] is an [integer], so [2147483647 + 1] overflows; [2147483648] is a [bigint] *)
Example pg_int4_overflow : fails PostgreSQL (fn "+" [int_max; int 1]) = true.
Proof. check. Qed.

Example pg_int8_no_overflow : text PostgreSQL (fn "+" [int 2147483648; int 1]) = "2147483649".
Proof. check. Qed.

Example pg_int8_overflow : fails PostgreSQL (fn "+" [big_max; int 1]) = true.
Proof. check. Qed.

(** a literal beyond the [bigint] range is a [numeric] *)
Example pg_numeric_literal : text PostgreSQL (fn "+" [int 9223372036854775808; int 1]) = "9223372036854775809".
Proof. check. Qed.

Example pg_cast_bigint : text PostgreSQL (fn "+" [fn "cast_bigint" [int_max]; int 1]) = "2147483648".
Proof. check. Qed.

(** MySQL: [BIGINT] arithmetic *)
Example my_int4_no_overflow : text MySQL (fn "+" [int_max; int 1]) = "2147483648".
Proof. check. Qed.

Example my_bigint_overflow : fails MySQL (fn "+" [big_max; int 1]) = true.
Proof. check. Qed.

(** [18446744073709551615] is a [BIGINT UNSIGNED]: [- 1] stays unsigned, [+ 1] overflows *)
Example my_unsigned : text MySQL (fn "-" [int 18446744073709551615; int 1]) = "18446744073709551614".
Proof. check. Qed.

Example my_unsigned_overflow : fails MySQL (fn "+" [int 18446744073709551615; int 1]) = true.
Proof. check. Qed.

(** SQLite: an overflow gives a REAL *)
Example lite_overflow_real : text SQLite (fn "cast_string" [fn "+" [big_max; int 1]]) = "9.22337203685478e+18".
Proof. check. Qed.

Definition bigs := values_ [c0] [[big_max]; [int 1]].

Example lite_sum_overflow : 
  match eval_query_result ORN (dialect_of SQLite) (_basesort _ init_db) (_instance _ init_db) 
          (to_dialect SQLite (select_where [as_ (agg "sum" (col c0)) c0] [from_as bigs [(c0, c0)]] c_true)) with
  | QR_Error _ => true
  | _ => false
  end = true.
Proof. check. Qed.

(** The text of an integer in PostgreSQL ([pg_strtoint32_safe]; the regression test [int4.sql]): the bases
    [0x], [0o], [0b], underscores between digits, a sign, spaces around. *)
Example pg_int_input :
  (text PostgreSQL (fn "cast_int" [str "0b100101"]), text PostgreSQL (fn "cast_int" [str "0o273"]),
   text PostgreSQL (fn "cast_int" [str "0x42F"]), text PostgreSQL (fn "cast_int" [str "-0x80000000"]),
   text PostgreSQL (fn "cast_int" [str "1_000_000"]), text PostgreSQL (fn "cast_int" [str "0x1EEE_FFFF"]),
   text PostgreSQL (fn "cast_int" [str "0b_10_0101"]), text PostgreSQL (fn "cast_bigint" [str "+4567890123456789"]),
   text PostgreSQL (fn "cast_int" [str "  12  "]))
  = ("37", "187", "1071", "-2147483648", "1000000", "518979583", "37", "4567890123456789", "12").
Proof. check. Qed.

Example pg_int_input_errors :
  (fails PostgreSQL (fn "cast_int" [str "_100"]), fails PostgreSQL (fn "cast_int" [str "100_"]),
   fails PostgreSQL (fn "cast_int" [str "1__000"]), fails PostgreSQL (fn "cast_int" [str "0x"]),
   fails PostgreSQL (fn "cast_int" [str "0b12"]), fails PostgreSQL (fn "cast_int" [str "0x80000000"]),
   fails PostgreSQL (fn "cast_int" [str "1 2"]), fails PostgreSQL (fn "cast_int" [str ""]))
  = (true, true, true, true, true, true, true, true).
Proof. check. Qed.
