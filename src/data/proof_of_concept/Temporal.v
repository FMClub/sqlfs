(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Dates, times, timestamps and intervals: the proleptic Gregorian calendar,     *)
(**   the texts which the engines read and print, and the arithmetic of dates.      *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String Ascii ZArith Bool DecimalString.

Import ListNotations.
Open Scope Z_scope.

(** * The calendar

    A date is a number of days from 1970-01-01 (negative before); the conversions are those of
    the proleptic Gregorian calendar, which every engine of the model uses for its [DATE]
    (PostgreSQL [date2j], MySQL [calc_daynr], SQLite [computeJD]). The algorithms are Howard Hinnant's
    [days_from_civil] and [civil_from_days]. *)
Definition days_from_civil (y m d : Z) : Z :=
  let y := if m <=? 2 then y - 1 else y in
  let era := (if y >=? 0 then y else y - 399) / 400 in
  let yoe := y - era * 400 in
  let mp := (m + 9) mod 12 in
  let doy := (153 * mp + 2) / 5 + d - 1 in
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy in
  era * 146097 + doe - 719468.

Definition civil_from_days (z : Z) : Z * Z * Z :=
  let z := z + 719468 in
  let era := (if z >=? 0 then z else z - 146096) / 146097 in
  let doe := z - era * 146097 in
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365 in
  let y := yoe + era * 400 in
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100) in
  let mp := (5 * doy + 2) / 153 in
  let d := doy - (153 * mp + 2) / 5 + 1 in
  let m := if mp <? 10 then mp + 3 else mp - 9 in
  (if m <=? 2 then y + 1 else y, m, d).

Definition is_leap (y : Z) : bool := (Z.eqb (y mod 4) 0 && negb (Z.eqb (y mod 100) 0)) || Z.eqb (y mod 400) 0.

Definition days_in_month (y m : Z) : Z :=
  match m with
  | 2 => if is_leap y then 29 else 28
  | 4 | 6 | 9 | 11 => 30
  | _ => 31
  end.

Definition valid_date (y m d : Z) : bool := (1 <=? m) && (m <=? 12) && (1 <=? d) && (d <=? days_in_month y m).

(** the day of the week, 0 for Sunday ([EXTRACT(DOW)]) *)
Definition day_of_week (days : Z) : Z := (days + 4) mod 7.

Definition day_of_year (days : Z) : Z :=
  let '(y, _, _) := civil_from_days days in days - days_from_civil y 1 1 + 1.

(** * Time of day and timestamps, in microseconds *)
Definition usec_per_day : Z := 86400000000.

(** a timestamp: microseconds from 1970-01-01 00:00:00 *)
Definition ts_of (days usec : Z) : Z := days * usec_per_day + usec.
Definition ts_days (ts : Z) : Z := ts / usec_per_day.
Definition ts_usec (ts : Z) : Z := ts mod usec_per_day.

(** [date + n months], the day being clamped to the last day of the month (PostgreSQL [timestamp_pl_interval],
    MySQL [date_add_interval] with [INTERVAL n MONTH]) *)
Definition add_months (days n : Z) : Z :=
  let '(y, m, d) := civil_from_days days in
  let t := y * 12 + (m - 1) + n in
  let y' := t / 12 in
  let m' := t mod 12 + 1 in
  days_from_civil y' m' (Z.min d (days_in_month y' m')).

(** * Texts *)
Definition string_of_Z (z : Z) : string := NilZero.string_of_int (Z.to_int z).

Fixpoint repeat_zero (n : nat) : string := match n with O => EmptyString | S n => String "0" (repeat_zero n) end.

Definition pad (w : nat) (z : Z) : string :=
  let s := string_of_Z (Z.abs z) in
  ((if Z.ltb z 0 then "-" else "") ++ repeat_zero (w - String.length s) ++ s)%string.

Definition date_text (days : Z) : string :=
  let '(y, m, d) := civil_from_days days in
  (pad 4 y ++ "-" ++ pad 2 m ++ "-" ++ pad 2 d)%string.

(** a time of day with [fsp] fractional digits (0 to 6), truncated *)
Definition time_text (usec : Z) (fsp : nat) : string :=
  let neg := Z.ltb usec 0 in
  let u := Z.abs usec in
  let s := u / 1000000 in
  let frac := u mod 1000000 in
  ((if neg then "-" else "") ++ pad 2 (s / 3600) ++ ":" ++ pad 2 ((s / 60) mod 60) ++ ":" ++ pad 2 (s mod 60) ++
   (match fsp with O => "" | _ => "." ++ substring 0 fsp (pad 6 frac) end))%string.

Definition timestamp_text (ts : Z) (fsp : nat) : string :=
  (date_text (ts_days ts) ++ " " ++ time_text (ts_usec ts) fsp)%string.

(** PostgreSQL prints the fractional seconds which are not zero, without trailing zeros *)
Fixpoint strip_trailing_zeros_aux (fuel : nat) (s : string) : string :=
  match fuel with
  | O => s
  | S f =>
    let n := String.length s in
    if Nat.ltb 0 n && Ascii.eqb (match get (n - 1) s with Some c => c | None => " "%char end) "0"
    then strip_trailing_zeros_aux f (substring 0 (n - 1) s) else s
  end.

Definition pg_time_text (usec : Z) : string :=
  let u := Z.abs usec in
  let frac := u mod 1000000 in
  let base := time_text (usec - (if Z.ltb usec 0 then - frac else frac)) 0 in
  if Z.eqb frac 0 then base else (base ++ "." ++ strip_trailing_zeros_aux 6 (pad 6 frac))%string.

Definition pg_timestamp_text (ts : Z) : string :=
  (date_text (ts_days ts) ++ " " ++ pg_time_text (ts_usec ts))%string.

(** * Parsing: [YYYY-MM-DD], [YYYY-MM-DD HH:MM:SS[.ffffff]], [HH:MM:SS[.ffffff]] *)
Definition digit (c : ascii) : option Z :=
  let n := Z.of_nat (nat_of_ascii c) in if (48 <=? n) && (n <=? 57) then Some (n - 48) else None.

Fixpoint digits_of (s : string) : option Z :=
  match s with
  | EmptyString => None
  | String c EmptyString => digit c
  | String c r => match digit c, digits_of r with
                  | Some d, Some v => Some (d * 10 ^ Z.of_nat (String.length r) + v)
                  | _, _ => None
                  end
  end.

(** split at a separator *)
Fixpoint split_at (sep : ascii) (s : string) : list string :=
  match s with
  | EmptyString => [EmptyString]
  | String c r => if Ascii.eqb c sep then EmptyString :: split_at sep r
                  else match split_at sep r with
                       | x :: l => String c x :: l
                       | nil => [String c EmptyString]
                       end
  end.

Definition parse_date (s : string) : option Z :=
  match split_at "-" s with
  | [y; m; d] => match digits_of y, digits_of m, digits_of d with
                 | Some y, Some m, Some d => if valid_date y m d then Some (days_from_civil y m d) else None
                 | _, _, _ => None
                 end
  | _ => None
  end.

(** microseconds of [HH:MM:SS[.ffffff]] *)
Definition parse_time (s : string) : option Z :=
  match split_at ":" s with
  | [h; mi; sec] =>
    let (whole, frac) := match split_at "." sec with
                         | [w; f] => (w, f)
                         | _ => (sec, EmptyString)
                         end in
    match digits_of h, digits_of mi, digits_of whole with
    | Some h, Some mi, Some se =>
      let f := match frac with
               | EmptyString => Some 0
               | _ => match digits_of (substring 0 6 (frac ++ "000000")) with Some v => Some v | None => None end
               end in
      match f with
      | Some f => if (mi <? 60) && (se <? 60) then Some (((h * 60 + mi) * 60 + se) * 1000000 + f) else None
      | None => None
      end
    | _, _, _ => None
    end
  | _ => None
  end.

Definition parse_timestamp (s : string) : option Z :=
  match split_at " " s with
  | [d] => match parse_date d with Some days => Some (ts_of days 0) | None => None end
  | [d; t] => match parse_date d, parse_time t with
              | Some days, Some u => if u <? usec_per_day then Some (ts_of days u) else None
              | _, _ => None
              end
  | _ => None
  end.
