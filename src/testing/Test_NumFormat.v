(************************************************************************************)
(**                                                                                 *)
(**                             The SQLFS Library                                   *)
(**                                                                                 *)
(************************************************************************************)

(** PostgreSQL [to_char (number, format)] (TODO 8.12, [PgNumFormat.v]): the examples of the table "to_char
    Examples" of the manual (section "Data Type Formatting Functions") which do not depend on the locale, and
    queries of the regression test [numeric.sql]. *)

Require Import List String ZArith QArith Qcanon.
Require Import IEEE Values PgNumFormat.
Import ListNotations.
Import NullValues.
Open Scope string_scope.

Ltac check := vm_compute; reflexivity.

(** [n / 10^s] as a [numeric], as a [float8], and an [integer] *)
Definition num (n : Z) (s : nat) := Value_D (Some (Q2Qc (Qmake n (Z.to_pos (10 ^ Z.of_nat s))), 20%nat, s)).
Definition f8 (n : Z) (s : nat) := VF false (round_q binary64 (Qmake n (Z.to_pos (10 ^ Z.of_nat s)))).
Definition int (n : Z) := Value_I (Some (n, 32%nat)).
Definition t (v : value) (f : string) : string :=
  match pg_num_to_char v f with Value_string (Some x) => x | _ => "ERROR" end.

(** the manual *)
Example manual_digits :
  (t (num (-1) 1) "99.99", t (num (-1) 1) "FM9.99", t (num (-1) 1) "FM90.99", t (num 1 1) "0.9",
   t (int 12) "9990999.9", t (int 12) "FM9990999.9", t (int 485) "999", t (int (-485)) "999",
   t (int 485) "9 9 9", t (int 1485) "9,999", t (num 1485 1) "999.999", t (num 1485 1) "FM999.999",
   t (num 1485 1) "FM999.990", t (num 314821 2) "9999.999")
  = ("  -.10", "-.1", "-0.1", " 0.1", "    0012.0", "0012.", " 485", "-485", " 4 8 5", " 1,485", " 148.500",
     "148.5", "148.500", " 3148.210").
Proof. check. Qed.

Example manual_signs :
  (t (int (-485)) "999S", t (int (-485)) "999MI", t (int 485) "999MI", t (int 485) "FM999MI",
   t (int 485) "PL999", t (int 485) "SG999", t (int (-485)) "SG999", t (int (-485)) "9SG99", t (int (-485)) "999PR")
  = ("485-", "485-", "485 ", "485", "+ 485", "+485", "-485", "4-85", "<485>").
Proof. check. Qed.

Example manual_others :
  (t (int 485) "RN", t (int 485) "FMRN", t (num 52 1) "FMRN", t (int 482) "999th", t (int 485) """Good number:""999",
   t (num 4858 1) """Pre:""999"" Post:"" .999", t (int 12) "99V999", t (num 124 1) "99V999", t (num 1245 2) "99V9",
   t (num 4859 7) "9.99EEEE")
  = ("        CDLXXXV", "CDLXXXV", "V", " 482nd", "Good number: 485", "Pre: 485 Post: .800", " 12000", " 12400",
     " 125", " 4.86e-04").
Proof. check. Qed.

(** [numeric.sql] *)
Example regress_fill :
  (t (num 100 0) "FM999.9", t (num 100 0) "FM999.", t (num 100 0) "FM999.SG ""items""", t (num 100 0) "FM999",
   t (f8 12345678901 0) "FM9999999999D9999900000000000000000")
  = ("100.", "100", "100+ items", "100", "##########.####").
Proof. check. Qed.

Example regress_roman :
  (t (num 100 0) "rn", t (num 1234 0) "rn", t (f8 1237 0) "fmrn", t (num 100000000000 0) "RN")
  = ("              c", "       mccxxxiv", "mccxxxvii", "###############").
Proof. check. Qed.

Example regress_literals :
  (t (num 100 0) "foo999", t (num 100 0) "f\oo999", t (num 100 0) "f\""oo999", t (num 100 0) "f""ool""999",
   t (num 100 0) "f""\ool""999", t (num 100 0) "f""ool\""999", t (num 100 0) "f""ool\\""999")
  = ("foo 100", "f\oo 100", "f""oo 100", "fool 100", "fool 100", "fool""999", "fool\ 100").
Proof. check. Qed.

Example regress_eeee :
  (t (num 99 0) "9EEEE", t (num (-99) 0) "9EEEE", t (num 9994 3) "9.99EEEE", t (num 9995 3) "9.99EEEE",
   t (num (-9995) 3) "9.99EEEE", t (num 0 0) "9.99EEEE", t (f8 4200000000 0) "9.999EEEE", t (f8 12 6) "9.999EEEE")
  = (" 1e+02", "-1e+02", " 9.99e+00", " 1.00e+01", "-1.00e+01", " 0.00e+00", " 4.200e+09", " 1.200e-05").
Proof. check. Qed.

Example regress_minus :
  (t (num 0 0) "MI9999999999.99", t (num (-42) 1) "MI9999999999.99", t (num 4200000000 0) "MI9999999999.99",
   t (num 12 6) "MI9999999999.99", t (num (-42) 1) "MI99.99")
  = ("           .00", "-         4.20", " 4200000000.00", "           .00", "- 4.20").
Proof. check. Qed.

(** the errors of the format *)
Example format_errors :
  (t (int 1) "9.9.9", t (int 1) "9PR9", t (int 1) "S9S", t (int 1) "9EEEE9", t (int 1) "RN9.9", t (int 1) "9V.9",
   t (int 1) "")
  = ("ERROR", "ERROR", "ERROR", "ERROR", "ERROR", "ERROR", "").
Proof. check. Qed.
