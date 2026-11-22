(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Tests of the scale of decimal numbers (TODO 1.2.1).                           *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String ZArith NArith.

Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.

Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax
        Dialects ValueKit PostgreSQL MySQL SQLite OceanBase MariaDB SpecRunner.

Import Tuple.
Import ListNotations.
Open Scope string_scope.

Ltac check := vm_compute; reflexivity.

Notation c0 := (Attr_Z "c0").

Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).

(** the text of the value of [e] *)
Definition text (d : vsem) (e : sexpr) : string :=
  match run d (select_where [as_ e c0] [] c_true) with
  | t :: nil => show_value (dot (TD d) t (out_attr 0))
  | _ => "?"
  end.

Definition holds (d : vsem) (c : scond) : bool :=
  Nat.eqb (List.length (run d (select_where [as_ (int 1) c0] [] c))) 1.

Definition d150 := cst (VD 150 2).

(** * PostgreSQL ([numeric.c]) *)

Example pg_literal : text PostgreSQL d150 = "1.50".
Proof. check. Qed.

(** the scale is not part of the value *)
Example pg_equal_scales : holds PostgreSQL (pred "=" [cst (VD 10 1); cst (VD 100 2)]) = true.
Proof. check. Qed.

Example pg_plus : text PostgreSQL (fn "+" [d150; int 1]) = "2.50".
Proof. check. Qed.

Example pg_mult : text PostgreSQL (fn "*" [d150; cst (VD 15 1)]) = "2.250".
Proof. check. Qed.

(** [select_div_scale]: at least 16 significant digits: [1 / 3.0] has 20 decimals *)
Example pg_div : text PostgreSQL (fn "/" [int 1; cst (VD 30 1)]) = "0.33333333333333333333".
Proof. check. Qed.

Example pg_div_large : text PostgreSQL (fn "/" [cst (VD 100000 1); int 3]) = "3333.3333333333333333".
Proof. check. Qed.

Example pg_round : text PostgreSQL (fn "round" [cst (VD 12345 3); int 2]) = "12.35".
Proof. check. Qed.

(** * The MySQL family ([strings/decimal.c]) *)

Example my_literal : text MySQL d150 = "1.50".
Proof. check. Qed.

Example my_length : text MySQL (fn "length" [cst (VD 0 2)]) = "4".
Proof. check. Qed.

Example my_div : text MySQL (fn "/" [int 4; int 3]) = "1.3333".
Proof. check. Qed.

(** the quotient holds 9 digits: [4/3 = 1.333333333] is true, [4/3 = 1.3333] is false *)
Example my_div_digits : 
  map (holds MySQL) [pred "=" [fn "/" [int 4; int 3]; cst (VD 1333333333 9)]; 
                     pred "=" [fn "/" [int 4; int 3]; cst (VD 13333 4)]] = [true; false].
Proof. check. Qed.

Example my_div_then_mult : text MySQL (fn "+" [fn "*" [fn "/" [int 4; int 3]; int 1000000]; int 1]) = "1333334.3330".
Proof. check. Qed.

(** a dividend with 6 decimals holds 2 units of 9 digits *)
Example my_div_two_units : 
  text MySQL (fn "+" [fn "*" [fn "/" [cst (VD 4000000 6); int 3]; int 1000000000]; int 1]) = "1333333334.3333333330".
Proof. check. Qed.

Example my_div_one_unit : 
  text MySQL (fn "+" [fn "*" [fn "/" [cst (VD 400000 5); int 3]; int 1000000000]; int 1]) = "1333333334.000000000".
Proof. check. Qed.

Definition one_two_five := values_ [c0] [[int 1]; [int 2]; [int 5]].

Example my_avg : 
  map (fun t => show_value (dot (TD MySQL) t (out_attr 0)))
      (run MySQL (select_where [as_ (agg "avg" (col c0)) c0] [from_as one_two_five [(c0, c0)]] c_true)) = ["2.6667"].
Proof. check. Qed.

Example maria_div : text MariaDB (fn "/" [cst (VD 10 1); int 3]) = "0.33333".
Proof. check. Qed.

(** * SQLite and Oracle: no display scale *)

Example lite_literal : text SQLite d150 = "1.5".
Proof. check. Qed.

Example ora_literal : text OceanBaseOracle d150 = "1.5".
Proof. check. Qed.

(** * [CAST(x AS DECIMAL(p, s))] *)

Example my_cast_decimal : text MySQL (fn "cast_decimal" [cst (VD 12345 3); int 5; int 2]) = "12.35".
Proof. check. Qed.

(** out of range: the largest value of the type (with a warning) *)
Example my_cast_decimal_clip : text MySQL (fn "cast_decimal" [int 1000; int 3; int 1]) = "99.9".
Proof. check. Qed.

Example pg_cast_numeric : text PostgreSQL (fn "cast_decimal" [cst (VD 12345 3); int 5; int 2]) = "12.35".
Proof. check. Qed.

(** out of range: an error *)
Example pg_cast_numeric_overflow : 
  match eval_query_result ORN (dialect_of PostgreSQL) (_basesort _ init_db) (_instance _ init_db) 
          (to_dialect PostgreSQL (select_where [as_ (fn "cast_decimal" [int 1000; int 3; int 1]) c0] [] c_true)) with
  | QR_Error _ => true
  | _ => false
  end = true.
Proof. check. Qed.

(** The text of a [numeric] with an exponent ([numeric_in]; [numeric.sql]): the scale is the number of
    decimals less the exponent, at least 0; [%] on NaN and the infinities (TODO 8.32) *)
Example pg_numeric_exponent :
  (text PostgreSQL (fn "cast_numeric" [str "4.2e9"]), text PostgreSQL (fn "cast_numeric" [str "1.2e-5"]),
   text PostgreSQL (fn "cast_numeric" [str "-7.777E+2"]), text PostgreSQL (fn "cast_numeric" [str "1.50e1"]))
  = ("4200000000", "0.000012", "-777.7", "15.0").
Proof. check. Qed.
(** [show_value] prints NaN as NULL: the special values are checked by their kind *)
Definition kind (d : vsem) (e : sexpr) : option IEEE.fspecial :=
  match run d (select_where [as_ e c0] [] c_true) with
  | t :: nil => match NullValues.float_parts (dot (TD d) t (out_attr 0)) with Some (sp, _, _) => Some sp | None => None end
  | _ => None
  end.
Example pg_numeric_special_mod :
  (kind PostgreSQL (fn "%" [fn "cast_numeric" [str "nan"]; str "0"]),
   kind PostgreSQL (fn "%" [fn "cast_numeric" [str "inf"]; str "2"]),
   text PostgreSQL (fn "%" [fn "cast_numeric" [str "4.2"]; fn "cast_numeric" [str "inf"]]),
   text PostgreSQL (fn "%" [fn "cast_numeric" [str "inf"]; str "0"]))
  = (Some IEEE.F_NaN, Some IEEE.F_NaN, "4.2", "ERROR").
Proof. check. Qed.

(** iteration 24: a double with an exponent ([float8in]: [strtod]); [log (b, x)] of [numeric] with an infinite
    or NaN argument ([numeric_log]) *)
Example pg_float_exponent :
  (text PostgreSQL (fn "cast_float8" [str "100e9"]), text PostgreSQL (fn "cast_float8" [str "-1.5E-3"]),
   text PostgreSQL (fn "cast_float8" [str "1e400"]))
  = ("100000000000", "-0.0015", "ERROR").
Proof. check. Qed.
Example pg_log_specials :
  (kind PostgreSQL (fn "log" [fn "cast_numeric" [str "0.5"]; str "inf"]),
   kind PostgreSQL (fn "log" [fn "cast_numeric" [str "2"]; str "inf"]),
   kind PostgreSQL (fn "log" [fn "cast_numeric" [str "inf"]; str "inf"]),
   kind PostgreSQL (fn "log" [fn "cast_numeric" [str "2"]; str "nan"]),
   text PostgreSQL (fn "log" [fn "cast_numeric" [str "inf"]; str "4.2"]),
   text PostgreSQL (fn "log" [fn "cast_numeric" [str "1"]; str "inf"]),
   text PostgreSQL (fn "log" [fn "cast_numeric" [str "-inf"]; str "2"]))
  = (Some IEEE.F_NegInf, Some IEEE.F_PosInf, Some IEEE.F_NaN, Some IEEE.F_NaN, "0", "ERROR", "ERROR").
Proof. check. Qed.

(** TODO 8.37: an infinity times a zero is NaN, an infinity divided by zero an error ([float8mul], [float8div]);
    [power] of a special [numeric] value gives a [numeric] ([0], not [-0]); [exp] of a large [numeric] has every
    digit; the power of a large integer exponent by the fixed point equals the exact one *)
Example special_products :
  (kind PostgreSQL (fn "*" [fn "cast_float8" [str "inf"]; fn "cast_float8" [str "0"]]),
   kind PostgreSQL (fn "*" [fn "cast_numeric" [str "-inf"]; fn "cast_numeric" [str "0"]]),
   text PostgreSQL (fn "/" [fn "cast_float8" [str "inf"]; fn "cast_float8" [str "0"]]),
   text PostgreSQL (fn "power" [fn "cast_numeric" [str "-inf"]; str "-3"]),
   kind PostgreSQL (fn "power" [fn "cast_float8" [str "-inf"]; fn "cast_float8" [str "-3"]]))
  = (Some IEEE.F_NaN, Some IEEE.F_NaN, "ERROR", "0", Some IEEE.F_NegZero).
Proof. check. Qed.
Example exp_digits_e :
  (match IEEE.exp_digits (QArith_base.inject_Z 1) 40 with
   | Some q => QArith_base.Qnum q * 10 ^ 30 / Zpos (QArith_base.Qden q) | None => 0 end)%Z
  = 2718281828459045235360287471352%Z.
Proof. check. Qed.
Example pow_round_fp :
  forallb (fun x => let '(a, b, n, r) := x in
                     NullValues.Qc_eq_bool (NullValues.pow_round a b n r) (NullValues.pow_round_exact a b n r))
          [(1234%Z, 1000%positive, 100%Z, 20%nat); (1234%Z, 1000%positive, (-100)%Z, 30%nat);
           ((-17)%Z, 10%positive, 77%Z, 5%nat); ((-17)%Z, 10%positive, (-65)%Z, 90%nat);
           (999999%Z, 1000000%positive, 300%Z, 40%nat)]
  = true.
Proof. check. Qed.
