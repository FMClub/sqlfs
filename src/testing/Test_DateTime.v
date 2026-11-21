(** * Date and time functions (TODO 2.7)

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

(** MySQL (manual 14.7) *)
Example dt_1 : text MySQL (fn "str_to_date" [s "01,5,2013"; s "%d,%m,%Y"]) = "2013-05-01".
Proof. check. Qed.

Example dt_2 : text MySQL (fn "str_to_date" [s "May 1, 2013"; s "%M %d,%Y"]) = "2013-05-01".
Proof. check. Qed.

Example dt_3 : text MySQL (fn "str_to_date" [s "a09:30:17"; s "a%h:%i:%s"]) = "09:30:17".
Proof. check. Qed.

Example dt_4 : text MySQL (fn "str_to_date" [s "09:30:17a"; s "%h:%i:%s"]) = "09:30:17".
Proof. check. Qed.

Example dt_5 : text MySQL (fn "str_to_date" [s "2013-07-01 10:20:30.123"; s "%Y-%m-%d %H:%i:%s.%f"]) = "2013-07-01 10:20:30.123000".
Proof. check. Qed.

Example dt_6 : text MySQL (fn "str_to_date" [s "2013-02-30"; s "%Y-%m-%d"]) = "NULL".
Proof. check. Qed.

Example dt_7 : text MySQL (fn "makedate" [int 2011; int 32]) = "2011-02-01".
Proof. check. Qed.

Example dt_8 : text MySQL (fn "makedate" [int 2011; int 0]) = "NULL".
Proof. check. Qed.

Example dt_9 : text MySQL (fn "maketime" [int 12; int 15; int 30]) = "12:15:30".
Proof. check. Qed.

Example dt_10 : text MySQL (fn "sec_to_time" [int 2378]) = "00:39:38".
Proof. check. Qed.

Example dt_11 : text MySQL (fn "time_to_sec" [fn "cast_time" [s "22:23:00"]]) = "80580".
Proof. check. Qed.

Example dt_12 : text MySQL (fn "from_days" [int 730669]) = "2000-07-03".
Proof. check. Qed.

Example dt_13 : text MySQL (fn "from_unixtime" [int 1447430881]) = "2015-11-13 16:08:01".
Proof. check. Qed.

Example dt_14 : text MySQL (fn "from_unixtime" [int 1447430881; s "%Y-%m-%d"]) = "2015-11-13".
Proof. check. Qed.

Example dt_15 : text MySQL (fn "dayname" [s "2007-02-03"]) = "Saturday".
Proof. check. Qed.

Example dt_16 : text MySQL (fn "monthname" [s "2008-02-03"]) = "February".
Proof. check. Qed.

Example dt_17 : text MySQL (fn "period_add" [int 200801; int 2]) = "200803".
Proof. check. Qed.

Example dt_18 : text MySQL (fn "period_diff" [int 200802; int 200703]) = "11".
Proof. check. Qed.

Example dt_19 : text MySQL (fn "timediff" [fn "cast_time" [s "10:00:00"]; fn "cast_time" [s "08:30:15"]]) = "01:29:45".
Proof. check. Qed.

Example dt_20 : text MySQL (fn "addtime" [fn "cast_time" [s "01:00:00"]; fn "cast_time" [s "02:30:00"]]) = "03:30:00".
Proof. check. Qed.

Example dt_21 : text MySQL (fn "time_format" [fn "cast_time" [s "10:05:03"]; s "%H.%i"]) = "10.05".
Proof. check. Qed.

Example dt_22 : text MySQL (fn "extract" [s "YEAR_MONTH"; s "2019-07-02 01:02:03"]) = "201907".
Proof. check. Qed.

Example dt_23 : text MySQL (fn "extract" [s "DAY_MINUTE"; s "2019-07-02 01:02:03"]) = "20102".
Proof. check. Qed.

Example dt_24 : text MySQL (fn "utc_date" []) = "2026-01-01".
Proof. check. Qed.


(** PostgreSQL (manual 9.9) *)
Example dt_25 : text PostgreSQL (fn "age" [fn "cast_timestamp" [s "2001-04-10"]; fn "cast_timestamp" [s "1957-06-13"]]) = "43 years 9 mons 27 days".
Proof. check. Qed.

Example dt_26 : text PostgreSQL (fn "to_date" [s "05 Dec 2000"; s "DD Mon YYYY"]) = "2000-12-05".
Proof. check. Qed.

Example dt_27 : text PostgreSQL (fn "to_timestamp" [s "05 Dec 2000"; s "DD Mon YYYY"]) = "2000-12-05 00:00:00+00".
Proof. check. Qed.

Example dt_28 : text PostgreSQL (fn "make_time" [int 8; int 15; cst (VD 235 1)]) = "08:15:23.5".
Proof. check. Qed.

Example dt_29 : text PostgreSQL (fn "make_timestamp" [int 2013; int 7; int 15; int 8; int 15; cst (VD 235 1)]) = "2013-07-15 08:15:23.5".
Proof. check. Qed.

Example dt_30 : text PostgreSQL (fn "make_interval" [int 0; int 0; int 0; int 10]) = "10 days".
Proof. check. Qed.

Example dt_31 : text PostgreSQL (fn "justify_days" [fn "cast_interval" [s "35 days"]]) = "1 mon 5 days".
Proof. check. Qed.

Example dt_32 : text PostgreSQL (fn "justify_hours" [fn "cast_interval" [s "27 hours"]]) = "1 day 03:00:00".
Proof. check. Qed.

Example dt_33 : text PostgreSQL (fn "date_bin" [fn "cast_interval" [s "15 minutes"]; fn "cast_timestamp" [s "2020-02-11 15:44:17"]; fn "cast_timestamp" [s "2001-01-01"]]) = "2020-02-11 15:30:00".
Proof. check. Qed.

Example dt_34 : fails PostgreSQL (fn "make_time" [int 25; int 0; int 0]) = true.
Proof. check. Qed.


(** Oracle (SQL Language Reference) *)
Example dt_35 : text OceanBaseOracle (fn "next_day" [fn "to_date" [s "15-OCT-2009"; s "DD-MON-YYYY"]; s "TUESDAY"]) = "2009-10-20 00:00:00".
Proof. check. Qed.

Example dt_36 : text OceanBaseOracle (fn "trunc" [fn "to_date" [s "27-OCT-1992"; s "DD-MON-YYYY"]; s "YEAR"]) = "1992-01-01 00:00:00".
Proof. check. Qed.

Example dt_37 : text OceanBaseOracle (fn "round" [fn "to_date" [s "27-OCT-2000"; s "DD-MON-YYYY"]; s "YEAR"]) = "2001-01-01 00:00:00".
Proof. check. Qed.

Example dt_38 : text OceanBaseOracle (fn "trunc" [fn "to_date" [s "27-OCT-1992 15:30:00"; s "DD-MON-YYYY HH24:MI:SS"]]) = "1992-10-27 00:00:00".
Proof. check. Qed.


(** the typed literals of the MySQL family (TiDB [expression/misc]; TODO 8.20): any punctuation between the fields
    of a [TIMESTAMP], which must have a date and a time; the formats of [TIME]; an invalid literal is an error *)
Definition my_lit (f t : string) : string :=
  match eval_query_result ORN (dialect_of MySQL) (_basesort _ init_db) (_instance _ init_db)
                          (to_dialect MySQL (select_where [as_ (fn "cast_string" [fn f [str t]]) c0] [] c_true)) with
  | QR_Error _ => "error"
  | QR_Rows _ (r :: _) => show_value (dot (TD MySQL) r (out_attr 0))
  | QR_Rows _ nil => "?"
  end.
Example lit_ts_1 : my_lit "lit_datetime" "2017@01@01 00~00~00" = "2017-01-01 00:00:00".
Proof. vm_compute; reflexivity. Qed.
Example lit_ts_2 : my_lit "lit_datetime" "2017@01@0001 00~00~00.333" = "2017-01-01 00:00:00.333".
Proof. vm_compute; reflexivity. Qed.
Example lit_ts_3 : my_lit "lit_datetime" "1992-01-03" = "error" /\ my_lit "lit_datetime" "00:00:00" = "error".
Proof. split; vm_compute; reflexivity. Qed.
Example lit_time_1 : my_lit "lit_time" "1 01:00:00" = "25:00:00".
Proof. vm_compute; reflexivity. Qed.
Example lit_time_2 : my_lit "lit_time" "-1:1:1.123454656" = "-01:01:01.123455".
Proof. vm_compute; reflexivity. Qed.
Example lit_time_3 : my_lit "lit_time" "21" = "00:00:21" /\ my_lit "lit_time" "1.1" = "00:00:01.1" /\ my_lit "lit_time" "20 20:20" = "500:20:00".
Proof. repeat split; vm_compute; reflexivity. Qed.
Example lit_time_4 : my_lit "lit_time" "2017-01-01 00:00:00" = "error" /\ my_lit "lit_time" "20171231235959.999999" = "error".
Proof. split; vm_compute; reflexivity. Qed.

(** [INTERVAL] of the MySQL family ([get_interval_value]; TiDB [expression/time]; TODO 8.23): the seconds keep their
    fraction, the other units take an integer (a decimal is rounded, a string gives the integer it starts with) *)
Definition my_plus (n : sexpr) (u : string) : string :=
  match eval_query_list ORN (dialect_of MySQL) (_basesort _ init_db) (_instance _ init_db)
          (to_dialect MySQL (select_where [as_ (fn "cast_string" [fn "date_add" [str "1900-01-01 00:00:00"; fn "interval" [n; str u]]]) c0] [] c_true)) with
  | r :: _ => show_value (dot (TD MySQL) r (out_attr 0))
  | nil => "?"
  end.
Example iv_sec_frac : my_plus (cst (VD 12 1)) "SECOND" = "1900-01-01 00:00:01.200000".
Proof. vm_compute; reflexivity. Qed.
Example iv_min_string : my_plus (str "1.9") "MINUTE" = "1900-01-01 00:01:00".
Proof. vm_compute; reflexivity. Qed.
Example iv_min_decimal : my_plus (cst (VD 19 1)) "MINUTE" = "1900-01-01 00:02:00".
Proof. vm_compute; reflexivity. Qed.
Example iv_micro : my_plus (cst (VD 19 1)) "MICROSECOND" = "1900-01-01 00:00:00.000002".
Proof. vm_compute; reflexivity. Qed.
Example iv_hour_string : my_plus (str "1e+3") "HOUR" = "1900-01-01 01:00:00".
Proof. vm_compute; reflexivity. Qed.
