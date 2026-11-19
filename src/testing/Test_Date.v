(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Tests of dates, times and intervals (TODO 1.5).                               *)
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

(** the text of [e] (with the dialect's cast to a string), or "ERROR" *)
Definition text (d : vsem) (e : sexpr) : string :=
  match run d (select_where [as_ (fn "cast_string" [e]) c0] [] c_true) with
  | QR_Rows _ (t :: nil) => show_value (dot (TD d) t c0)
  | QR_Error _ => "ERROR"
  | _ => "?"
  end.

Definition dt (d : string) := fn "cast_date" [str d].
Definition ts (t : string) := fn "cast_timestamp" [str t].

(** * PostgreSQL *)

Example pg_date_plus : text PostgreSQL (fn "+" [dt "2024-02-29"; int 1]) = "2024-03-01".
Proof. check. Qed.

Example pg_date_minus : text PostgreSQL (fn "-" [dt "2024-03-01"; dt "2024-02-01"]) = "29".
Proof. check. Qed.

(** the day is clamped to the end of the month *)
Example pg_plus_month : text PostgreSQL (fn "+" [dt "2024-01-31"; fn "cast_interval" [str "1 month"]]) = "2024-02-29 00:00:00".
Proof. check. Qed.

Example pg_ts_minus : text PostgreSQL (fn "-" [ts "2024-01-02 03:00:00"; ts "2024-01-01 00:00:00"]) = "1 day 03:00:00".
Proof. check. Qed.

Example pg_interval_text : text PostgreSQL (fn "cast_interval" [str "1 year 2 months 3 days"]) = "1 year 2 mons 3 days".
Proof. check. Qed.

Example pg_extract_dow : text PostgreSQL (fn "extract" [str "dow"; dt "2024-11-19"]) = "2".
Proof. check. Qed.

Example pg_extract_second : text PostgreSQL (fn "extract" [str "second"; ts "2024-01-01 10:00:59.5"]) = "59.500000".
Proof. check. Qed.

Example pg_date_trunc : text PostgreSQL (fn "date_trunc" [str "month"; ts "2024-03-15 10:00:00"]) = "2024-03-01 00:00:00".
Proof. check. Qed.

Example pg_to_char : text PostgreSQL (fn "to_char" [ts "2024-03-05 14:07:09"; str "YYYY-MM-DD HH24:MI:SS Dy"]) = "2024-03-05 14:07:09 Tue".
Proof. check. Qed.

Example pg_bad_date : text PostgreSQL (dt "2024-02-30") = "ERROR".
Proof. check. Qed.

Definition holds (d : vsem) (c : scond) : bool :=
  match run d (select_where [as_ (int 1) (Attr_Z "c1")] [] c) with QR_Rows _ (_ :: _) => true | _ => false end.

(** a string compared with a date is read as a date *)
Example pg_compare_string : holds PostgreSQL (pred "<" [dt "2024-01-01"; str "2024-06-01"]) = true.
Proof. check. Qed.

(** * MySQL *)

Example my_plus_interval : text MySQL (fn "+" [dt "2024-01-31"; fn "interval" [int 1; str "MONTH"]]) = "2024-02-29".
Proof. check. Qed.

Example my_date_add_string : text MySQL (fn "date_add" [str "2024-01-31"; fn "interval" [int 1; str "DAY"]]) = "2024-02-01".
Proof. check. Qed.

Example my_date_add_hour : text MySQL (fn "date_add" [str "2024-01-31"; fn "interval" [int 2; str "HOUR"]]) = "2024-01-31 02:00:00".
Proof. check. Qed.

Example my_datediff : text MySQL (fn "datediff" [str "2024-03-01"; str "2024-02-01"]) = "29".
Proof. check. Qed.

(** whole months: from January 31 to February 29 is not a month *)
Example my_timestampdiff : text MySQL (fn "timestampdiff" [str "MONTH"; str "2024-01-31"; str "2024-02-29"]) = "0".
Proof. check. Qed.

(** a date used as a number is [YYYYMMDD] *)
Example my_date_number : text MySQL (fn "+" [dt "2024-01-01"; int 1]) = "20240102".
Proof. check. Qed.

Example my_date_format : text MySQL (fn "date_format" [str "2024-03-05 14:07:09"; str "%W %M %e %Y %T"]) = "Tuesday March 5 2024 14:07:09".
Proof. check. Qed.

(** [WEEK] mode 0: 2024-01-01 is a Monday, before the first Sunday *)
Example my_week : text MySQL (fn "week" [str "2024-01-01"]) = "0".
Proof. check. Qed.

Example my_bad_date : text MySQL (dt "abc") = "NULL".
Proof. check. Qed.

Example my_now : text MySQL (fn "now" []) = "2026-01-01 12:00:00".
Proof. check. Qed.

(** * SQLite: dates are texts *)

(** a month modifier does not clamp the day *)
Example lite_plus_month : text SQLite (fn "date" [str "2024-01-31"; str "+1 month"]) = "2024-03-02".
Proof. check. Qed.

Example lite_minutes : text SQLite (fn "datetime" [str "2024-01-01 10:00:00"; str "+90 minutes"]) = "2024-01-01 11:30:00".
Proof. check. Qed.

Example lite_strftime : text SQLite (fn "strftime" [str "%Y-%j"; str "2024-03-01"]) = "2024-061".
Proof. check. Qed.

Example lite_julianday : text SQLite (fn "julianday" [str "2000-01-01"]) = "2451544.5".
Proof. check. Qed.

Example lite_start_of_month : text SQLite (fn "date" [str "2024-03-15"; str "start of month"; str "-1 day"]) = "2024-02-29".
Proof. check. Qed.

(** * Oracle mode *)

Definition od (s : string) := fn "to_date" [str s; str "YYYY-MM-DD"].

Example ora_plus : text OceanBaseOracle (fn "to_char" [fn "+" [od "2024-03-05"; int 1]; str "YYYY-MM-DD"]) = "2024-03-06".
Proof. check. Qed.

Example ora_minus : text OceanBaseOracle (fn "-" [od "2024-03-05"; od "2024-03-01"]) = "4".
Proof. check. Qed.

(** the last day of a month gives the last day of the result month *)
Example ora_add_months : text OceanBaseOracle (fn "to_char" [fn "add_months" [od "2024-02-29"; int 1]; str "YYYY-MM-DD"]) = "2024-03-31".
Proof. check. Qed.

Example ora_months_between : text OceanBaseOracle (fn "months_between" [od "2024-03-31"; od "2024-02-29"]) = "1".
Proof. check. Qed.

(** [NLS_DATE_FORMAT] = ['DD-MON-RR'] *)
Example ora_default_text : text OceanBaseOracle (fn "to_char" [od "2024-03-05"]) = "05-MAR-24".
Proof. check. Qed.

(** a separator of the format matches any separator, a number must be a number *)
Example ora_separator : text OceanBaseOracle (fn "to_char" [fn "to_date" [str "2024/03/05"; str "YYYY-MM-DD"]; str "YYYY-MM-DD"]) = "2024-03-05".
Proof. check. Qed.

Example ora_bad_format : text OceanBaseOracle (fn "to_date" [str "abcd-03-05"; str "YYYY-MM-DD"]) = "ERROR".
Proof. check. Qed.
