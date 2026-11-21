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
  (* the division of Coq rounds down, as the algorithm needs (in C it truncates and is corrected by hand) *)
  let era := y / 400 in
  let yoe := y - era * 400 in
  let mp := (m + 9) mod 12 in
  let doy := (153 * mp + 2) / 5 + d - 1 in
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy in
  era * 146097 + doe - 719468.

Definition civil_from_days (z : Z) : Z * Z * Z :=
  let z := z + 719468 in
  let era := z / 146097 in
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

(** a year before the common era is printed as PostgreSQL does: the year 0 of the calendar is [0001 ... BC] *)
Definition date_text (days : Z) : string :=
  let '(y, m, d) := civil_from_days days in
  if Z.leb y 0 then (pad 4 (1 - y) ++ "-" ++ pad 2 m ++ "-" ++ pad 2 d ++ " BC")%string
  else (pad 4 y ++ "-" ++ pad 2 m ++ "-" ++ pad 2 d)%string.

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

(** [YYYY-MM-DD], with an optional era [AD] or [BC] after it (PostgreSQL): the year [Y BC] is the year [1 - Y] of
    the proleptic calendar *)
Definition parse_date (s : string) : option Z :=
  let n := String.length s in
  let suffix := if Nat.leb 3 n then substring (n - 3) 3 s else EmptyString in
  let '(bc, s) := if String.eqb suffix " BC" then (true, substring 0 (n - 3) s)
                  else if String.eqb suffix " AD" then (false, substring 0 (n - 3) s)
                  else (false, s) in
  match split_at "-" s with
  | [y; m; d] => match digits_of y, digits_of m, digits_of d with
                 | Some y, Some m, Some d =>
                   let y := if bc then 1 - y else y in
                   if valid_date y m d && (negb bc || Z.ltb y 1) then Some (days_from_civil y m d) else None
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
  (* [HH:MM]: the seconds are 0 *)
  | [h; mi] => match digits_of h, digits_of mi with
               | Some h, Some mi => if mi <? 60 then Some ((h * 60 + mi) * 60 * 1000000) else None
               | _, _ => None
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

(** * Weeks *)

(** ISO 8601: the week starts on Monday, week 1 contains the first Thursday of the year *)
Definition iso_weekday (days : Z) : Z := let w := day_of_week days in if w =? 0 then 7 else w.

Definition iso_week_year (days : Z) : Z * Z :=
  let thursday := days - iso_weekday days + 4 in
  let '(y, _, _) := civil_from_days thursday in
  (y, (thursday - days_from_civil y 1 1) / 7 + 1).

(** * Intervals (PostgreSQL): months, days and microseconds, kept apart *)

Definition plural (n : Z) (unit : string) : string :=
  (string_of_Z n ++ " " ++ unit ++ (if Z.eqb (Z.abs n) 1 then "" else "s"))%string.

(** [interval_out] with [IntervalStyle] = [postgres]: [1 year 2 mons 3 days 04:05:06] *)
Definition pg_interval_text (months days usec : Z) : string :=
  let y := Z.quot months 12 in
  let mo := Z.rem months 12 in
  let parts := (if Z.eqb y 0 then nil else [plural y "year"]) ++
               (if Z.eqb mo 0 then nil else [if Z.eqb (Z.abs mo) 1 then (string_of_Z mo ++ " mon")%string else (string_of_Z mo ++ " mons")%string]) ++
               (if Z.eqb days 0 then nil else [plural days "day"]) ++
               (if Z.eqb usec 0 then nil else [pg_time_text usec]) in
  match parts with
  | nil => "00:00:00"
  | p :: r => fold_left (fun acc x => (acc ++ " " ++ x)%string) r p
  end.

(** [n unit] for an interval literal or [INTERVAL n unit] *)
Definition interval_of_unit (n : Z) (unit : string) : option (Z * Z * Z) :=
  match unit with
  | "year" | "years" | "YEAR" => Some (n * 12, 0, 0)
  | "month" | "months" | "mon" | "mons" | "MONTH" => Some (n, 0, 0)
  | "week" | "weeks" | "WEEK" => Some (0, n * 7, 0)
  | "day" | "days" | "DAY" => Some (0, n, 0)
  | "hour" | "hours" | "HOUR" => Some (0, 0, n * 3600000000)
  | "minute" | "minutes" | "min" | "mins" | "MINUTE" => Some (0, 0, n * 60000000)
  | "second" | "seconds" | "sec" | "secs" | "SECOND" => Some (0, 0, n * 1000000)
  | "microsecond" | "microseconds" | "MICROSECOND" => Some (0, 0, n)
  | "quarter" | "QUARTER" => Some (n * 3, 0, 0)
  | _ => None
  end%string.

(** [timestamp + interval]: the months (the day clamped), then the days, then the microseconds *)
Definition ts_plus_interval (ts : Z) (iv : Z * Z * Z) : Z :=
  let '(mo, d, us) := iv in
  ts_of (add_months (ts_days ts) mo + d) (ts_usec ts) + us.

(** * The time of the statement

    [now()], [CURRENT_DATE], [CURRENT_TIMESTAMP], [SYSDATE] are the time at which the statement
    starts; the model takes it as a parameter of the environment, fixed here to
    2026-01-01 12:00:00 UTC (a query which reads it has this value in all the dialects). *)
Definition statement_time : Z := ts_of (days_from_civil 2026 1 1) (12 * 3600000000).

(** * Formats *)

Definition month_names : list string :=
  ["January"; "February"; "March"; "April"; "May"; "June"; "July"; "August"; "September"; "October"; "November"; "December"]%string.
Definition day_names : list string := ["Sunday"; "Monday"; "Tuesday"; "Wednesday"; "Thursday"; "Friday"; "Saturday"]%string.

Definition upper_ascii (c : ascii) : ascii :=
  let n := nat_of_ascii c in if (Nat.leb 97 n && Nat.leb n 122)%bool then ascii_of_nat (n - 32) else c.
Fixpoint upper_string (s : string) : string := match s with EmptyString => EmptyString | String c r => String (upper_ascii c) (upper_string r) end.

Definition month_name (m : Z) : string := nth (Z.to_nat (m - 1)) month_names EmptyString.
Definition day_name (dow : Z) : string := nth (Z.to_nat dow) day_names EmptyString.

(** MySQL [DATE_FORMAT] ([Item_func_date_format], [make_date_time]): [%Y %y %m %c %d %e %H %k %h %I %l %i %s %S
    %f %p %M %b %W %a %j %w %T %r %%]; another character after [%] is itself *)
Fixpoint my_format (fuel : nat) (ts : Z) (fmt : string) : string :=
  match fuel with
  | O => EmptyString
  | S f =>
    match fmt with
    | EmptyString => EmptyString
    | String "%" (String c r) =>
      let days := ts_days ts in
      let '(y, m, d) := civil_from_days days in
      let us := ts_usec ts in
      let h := us / 3600000000 in
      let mi := (us / 60000000) mod 60 in
      let se := (us / 1000000) mod 60 in
      let h12 := let x := h mod 12 in if Z.eqb x 0 then 12 else x in
      let piece :=
          match c with
          | "Y" => pad 4 y | "y" => pad 2 (y mod 100) | "m" => pad 2 m | "c" => string_of_Z m
          | "d" => pad 2 d | "e" => string_of_Z d | "H" => pad 2 h | "k" => string_of_Z h
          | "h" | "I" => pad 2 h12 | "l" => string_of_Z h12 | "i" => pad 2 mi
          | "s" | "S" => pad 2 se | "f" => pad 6 (us mod 1000000)
          | "p" => if Z.ltb h 12 then "AM"%string else "PM"%string
          | "M" => month_name m | "b" => substring 0 3 (month_name m)
          | "W" => day_name (day_of_week days) | "a" => substring 0 3 (day_name (day_of_week days))
          | "j" => pad 3 (day_of_year days) | "w" => string_of_Z (day_of_week days)
          | "T" => (pad 2 h ++ ":" ++ pad 2 mi ++ ":" ++ pad 2 se)%string
          | "r" => (pad 2 h12 ++ ":" ++ pad 2 mi ++ ":" ++ pad 2 se ++ " " ++ (if Z.ltb h 12 then "AM" else "PM"))%string
          | _ => String c EmptyString
          end%char in
      (piece ++ my_format f ts r)%string
    | String c r => String c (my_format f ts r)
    end
  end.

Open Scope string_scope.

Fixpoint repeat_space (n : nat) : string := match n with O => EmptyString | S k => String " " (repeat_space k) end.

(** PostgreSQL [to_char] and Oracle [TO_CHAR] for dates: the patterns [YYYY YY MM DD HH24 HH12 HH MI SS MS US
    Month Mon Day Dy AM PM Q DDD D WW]; the other characters are copied. *)
Fixpoint pg_format (fuel : nat) (ts : Z) (fmt : string) : string :=
  match fuel with
  | O => EmptyString
  | S f =>
    let days := ts_days ts in
    let '(y, m, d) := civil_from_days days in
    let us := ts_usec ts in
    let h := us / 3600000000 in
    let mi := (us / 60000000) mod 60 in
    let se := (us / 1000000) mod 60 in
    let h12 := let x := h mod 12 in if Z.eqb x 0 then 12 else x in
    let take (p : string) := String.prefix p fmt in
    let rest (p : string) := substring (String.length p) (String.length fmt - String.length p) fmt in
    let try (p out : string) (k : string -> string) (otherwise : string) := if take p then (out ++ k (rest p))%string else otherwise in
    let go := pg_format f ts in
    match fmt with
    | EmptyString => EmptyString
    | String c r =>
      try "YYYY" (pad 4 y) go (try "YY" (pad 2 (y mod 100)) go (try "MM" (pad 2 m) go (try "DDD" (pad 3 (day_of_year days)) go
      (try "DD" (pad 2 d) go (try "HH24" (pad 2 h) go (try "HH12" (pad 2 h12) go (try "HH" (pad 2 h12) go
      (try "MI" (pad 2 mi) go (try "SS" (pad 2 se) go (try "MS" (pad 3 ((us / 1000) mod 1000)) go (try "US" (pad 6 (us mod 1000000)) go
      (try "Month" (let n := month_name m in (n ++ repeat_space (9 - String.length n))%string) go
      (try "MONTH" (let n := upper_string (month_name m) in (n ++ repeat_space (9 - String.length n))%string) go
      (try "Mon" (substring 0 3 (month_name m)) go (try "MON" (upper_string (substring 0 3 (month_name m))) go
      (try "Day" (let n := day_name (day_of_week days) in (n ++ repeat_space (9 - String.length n))%string) go
      (try "Dy" (substring 0 3 (day_name (day_of_week days))) go
      (try "AM" (if Z.ltb h 12 then "AM" else "PM") go (try "PM" (if Z.ltb h 12 then "AM" else "PM") go
      (try "Q" (string_of_Z ((m - 1) / 3 + 1)) go (try "D" (string_of_Z (day_of_week days + 1)) go
      (try "WW" (pad 2 ((day_of_year days - 1) / 7 + 1)) go
      (String c (go r))))))))))))))))))))))))
    end
  end.
