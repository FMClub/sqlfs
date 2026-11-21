(** * Mathematical functions (TODO 2.1)

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
Definition two_0 := cst (VD 20 1).

Example math_1 : text PostgreSQL (fn "sqrt" [int 2]) = "1.4142135623730951".
Proof. check. Qed.

Example math_2 : text PostgreSQL (fn "sqrt" [two_0]) = "1.414213562373095".
Proof. check. Qed.

Example math_3 : text PostgreSQL (fn "exp" [cst (VD 10 1)]) = "2.7182818284590452".
Proof. check. Qed.

Example math_4 : text PostgreSQL (fn "ln" [cst (VD 100 1)]) = "2.3025850929940457".
Proof. check. Qed.

Example math_5 : text PostgreSQL (fn "log" [cst (VD 1000 1)]) = "2.0000000000000000".
Proof. check. Qed.

Example math_6 : text PostgreSQL (fn "ln" [int 2]) = "0.6931471805599453".
Proof. check. Qed.

Example math_7 : text PostgreSQL (fn "exp" [int 1]) = "2.718281828459045".
Proof. check. Qed.

Example math_8 : fails PostgreSQL (fn "sqrt" [int (-1)]) = true.
Proof. check. Qed.

Example math_9 : text PostgreSQL (fn "degrees" [int 1]) = "57.29577951308232".
Proof. check. Qed.

Example math_10 : text PostgreSQL (fn "radians" [int 180]) = "3.141592653589793".
Proof. check. Qed.

Example math_11 : text PostgreSQL (fn "pi" []) = "3.141592653589793".
Proof. check. Qed.

Example math_12 : text PostgreSQL (fn "cbrt" [int 27]) = "3".
Proof. check. Qed.

Example math_13 : text PostgreSQL (fn "power" [int 2; int 10]) = "1024".
Proof. check. Qed.

Example math_14 : text PostgreSQL (fn "power" [dbl 2; cst (VFl false 5 (-1))]) = "1.4142135623730951".
Proof. check. Qed.

Example math_15 : text PostgreSQL (fn "atan2" [int 1; int 1]) = "0.7853981633974483".
Proof. check. Qed.

Example math_16 : text PostgreSQL (fn "exp" [cst (VD 1000 1)]) = "26881171418161354484126255515800135873611118.8".
Proof. check. Qed.

Example math_17 : text MySQL (fn "sqrt" [int 2]) = "1.4142135623730951".
Proof. check. Qed.

Example math_18 : text MySQL (fn "sqrt" [int (-1)]) = "NULL".
Proof. check. Qed.

Example math_19 : text MySQL (fn "pi" []) = "3.141593".
Proof. check. Qed.

Example math_20 : text MySQL (fn "log" [int 2; int 8]) = "3".
Proof. check. Qed.

Example math_21 : text MySQL (fn "log2" [int 8]) = "3".
Proof. check. Qed.

Example math_22 : text MySQL (fn "degrees" [fn "pi" []]) = "180".
Proof. check. Qed.

Example math_23 : fails MySQL (fn "exp" [int 1000]) = true.
Proof. check. Qed.

Example math_24 : text MySQL (fn "pow" [int 2; cst (VD 5 1)]) = "1.4142135623730951".
Proof. check. Qed.

Example math_25 : text SQLite (fn "log" [int 100]) = "2.0".
Proof. check. Qed.

Example math_26 : text SQLite (fn "pi" []) = "3.14159265358979".
Proof. check. Qed.

Example math_27 : text SQLite (fn "exp" [int 1000]) = "Inf".
Proof. check. Qed.

Example math_28 : text SQLite (fn "sqrt" [int (-1)]) = "NULL".
Proof. check. Qed.

Example math_29 : text SQLite (fn "pow" [int 2; cst (VD 5 1)]) = "1.4142135623731".
Proof. check. Qed.


(** Bits and integers *)
Example bits_101 : text MySQL (fn "&" [int 12; int 10]) = "8".
Proof. check. Qed.

Example bits_102 : text MySQL (fn "~" [int 0]) = "18446744073709551615".
Proof. check. Qed.

Example bits_103 : text MySQL (fn "<<" [int 1; int 64]) = "0".
Proof. check. Qed.

Example bits_104 : text MySQL (fn "|" [int (-1); int 0]) = "18446744073709551615".
Proof. check. Qed.

Example bits_105 : text MySQL (fn "bit_count" [int 255]) = "8".
Proof. check. Qed.

Example bits_106 : text MySQL (fn "rand" [int 3]) = "0.9057697559760601".
Proof. check. Qed.

Example bits_107 : text SQLite (fn "~" [int 0]) = "-1".
Proof. check. Qed.

Example bits_108 : text SQLite (fn ">>" [int (-8); int 1]) = "-4".
Proof. check. Qed.

Example bits_109 : text SQLite (fn "<<" [int 1; int (-1)]) = "0".
Proof. check. Qed.

Example bits_110 : text PostgreSQL (fn "#" [int 12; int 10]) = "6".
Proof. check. Qed.

Example bits_111 : text PostgreSQL (fn "<<" [int 1; int 31]) = "-2147483648".
Proof. check. Qed.

Example bits_112 : text PostgreSQL (fn "gcd" [int 12; int 18]) = "6".
Proof. check. Qed.

Example bits_113 : text PostgreSQL (fn "lcm" [int 4; int 6]) = "12".
Proof. check. Qed.

Example bits_114 : text PostgreSQL (fn "gcd" [cst (VD 15 1); cst (VD 9 1)]) = "0.3".
Proof. check. Qed.

Example bits_115 : text PostgreSQL (fn "lcm" [cst (VD 15 1); cst (VD 9 1)]) = "4.5".
Proof. check. Qed.

Example bits_116 : text PostgreSQL (fn "factorial" [int 20]) = "2432902008176640000".
Proof. check. Qed.

Example bits_117 : text PostgreSQL (fn "width_bucket" [cst (VD 53 1); int 0; int 10; int 5]) = "3".
Proof. check. Qed.

Example bits_118 : fails PostgreSQL (fn "factorial" [int (-1)]) = true.
Proof. check. Qed.

Example lite_ceil_int : text SQLite (fn "ceil" [int 3]) = "3".
Proof. check. Qed.
Example lite_ceil_real : text SQLite (fn "ceil" [cst (VD 25 1)]) = "3.0".
Proof. check. Qed.
Example lite_trunc : text SQLite (fn "trunc" [cst (VD (-25) 1)]) = "-2.0".
Proof. check. Qed.
Example pg_ceiling : text PostgreSQL (fn "ceiling" [cst (VD 25 1)]) = "3".
Proof. check. Qed.
Example pg_random : fails PostgreSQL (fn "random" []) = true.
Proof. check. Qed.

(** [power] of [numeric] (PostgreSQL regression test [numeric]): the scale gives 16 significant digits and at least
    the scales of the arguments; an integer exponent is exact; a string literal by a [numeric] is a [numeric] *)
Example pg_pow_1 : text PostgreSQL (fn "power" [cst (VD 12 2); cst (VD (-20) 0)]) = "2608405330458882702.55".
Proof. check. Qed.
Example pg_pow_2 : text PostgreSQL (fn "power" [cst (VD 123 1); cst (VD 456 1)]) = "50081010321492803393171165777624533697036806969694.9".
Proof. check. Qed.
Example pg_pow_3 : text PostgreSQL (fn "power" [fn "cast_numeric" [str "-2"]; str "-1"]) = "-0.5000000000000000".
Proof. check. Qed.
Example pg_pow_4 : text PostgreSQL (fn "power" [cst (VD 0 1); cst (VD 0 1)]) = "1.0000000000000000".
Proof. check. Qed.
Example pg_pow_5 : fails PostgreSQL (fn "power" [cst (VD (-1234) 2); cst (VD 5 1)]) = true.
Proof. check. Qed.

(** [power] and [exp] of [double precision] on NaN and the infinities ([dpow], [dexp] of [float.c]) *)
Definition f8 (t : string) := fn "cast_float8" [str t].
Example pg_dpow_1 : text PostgreSQL (fn "power" [f8 "NaN"; f8 "0"]) = "1".
Proof. check. Qed.
Example pg_dpow_2 : text PostgreSQL (fn "power" [f8 "1"; f8 "NaN"]) = "1".
Proof. check. Qed.
Example pg_dpow_3 : text PostgreSQL (fn "power" [f8 "-inf"; f8 "3"]) = "-Infinity".
Proof. check. Qed.
Example pg_dpow_4 : text PostgreSQL (fn "power" [f8 "0.1"; f8 "-inf"]) = "Infinity".
Proof. check. Qed.
Example pg_dpow_5 : text PostgreSQL (fn "power" [f8 "-1"; f8 "inf"]) = "1".
Proof. check. Qed.
Example pg_dexp_inf : text PostgreSQL (fn "exp" [f8 "inf"]) = "Infinity" /\ text PostgreSQL (fn "exp" [f8 "-inf"]) = "0".
Proof. split; check. Qed.
Example pg_nan_by_zero : text PostgreSQL (fn "/" [f8 "nan"; f8 "0"]) = "NaN".
Proof. check. Qed.
Example pg_series_numeric :
  List.length (run PostgreSQL (select_star_where [from_fun "generate_series" [fn "cast_numeric" [int 1]; fn "cast_numeric" [int 3]] false [c0]] c_true)) = 3%nat.
Proof. check. Qed.

(** [NaN] and the infinities of [numeric] (TODO 8.11): they are the special values of the doubles; a string
    literal by a number is read as a [numeric] *)
Definition num (t : string) := fn "cast_numeric" [str t].
Example pg_num_nan : text PostgreSQL (num "NaN") = "NaN" /\ text PostgreSQL (num "-Infinity") = "-Infinity".
Proof. split; check. Qed.
Example pg_num_nan_div : text PostgreSQL (fn "/" [num "nan"; str "0"]) = "NaN".
Proof. check. Qed.
Example pg_num_inf_pow : text PostgreSQL (fn "power" [num "-inf"; str "3"]) = "-Infinity".
Proof. check. Qed.
Example pg_num_pow_inf : text PostgreSQL (fn "power" [num "-2"; str "-inf"]) = "0".
Proof. check. Qed.
Example pg_num_to_float4 : text PostgreSQL (fn "cast_float4" [num "Infinity"]) = "Infinity".
Proof. check. Qed.
Example pg_float_to_num : text PostgreSQL (fn "cast_numeric" [f8 "NaN"]) = "NaN".
Proof. check. Qed.
Example pg_lit_plus : text PostgreSQL (fn "+" [str "1.5"; int 1]) = "2.5".
Proof. check. Qed.
