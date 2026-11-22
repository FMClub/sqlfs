(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Date and time functions (TODO 2.7): the functions of the MySQL family,        *)
(**   PostgreSQL and Oracle which Phase 1.5 did not cover.                          *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String Ascii ZArith QArith Qcanon Bool.

Require Import IEEE Temporal Values ValueKit StringFuns.

Import ListNotations.
Import NullValues.
Open Scope Z_scope.
Open Scope bool_scope.

Definition usec_s : Z := 1000000.
Definition usec_h : Z := 3600000000.

(** * MySQL [STR_TO_DATE (s, fmt)] ([extract_date_time], [sql/item_timefunc.cc])

    The specifiers [%Y %y %m %c %d %e %H %k %h %I %l %i %s %S %f %p %M %b %a %W %j %T %r %%]; another
    character of the format must be in the text. The result is a [DATE] when the format has only date
    parts, a [TIME] when it has only time parts, a [DATETIME] otherwise ([DATETIME(6)] with [%f]). A
    month or a day which is not given is 0 in MySQL (a "zero date"): the model has no such date and
    gives NULL; an invalid date is NULL. *)
Record sfields := mk_sf { sf_y : option Z; sf_mo : option Z; sf_d : option Z; sf_h : Z; sf_mi : Z; sf_s : Z;
                          sf_us : Z; sf_pm : option bool; sf_doy : option Z; sf_date : bool; sf_time : bool; sf_frac : bool }.

Definition sf0 := mk_sf None None None 0 0 0 0 None None false false false.

(** at most [k] digits *)
Fixpoint take_digits (k : nat) (s : list Z) (acc : Z) (n : nat) : option (Z * nat * list Z) :=
  match k, s with
  | S k', c :: r => if is_digit_cp c then take_digits k' r (acc * 10 + c - 48) (S n)
                    else if Nat.eqb n 0 then None else Some (acc, n, s)
  | _, _ => if Nat.eqb n 0 then None else Some (acc, n, s)
  end.

Definition name_match (names : list string) (len3 : bool) (s : list Z) : option (Z * list Z) :=
  let fix go (i : Z) (l : list string) :=
      match l with
      | nil => None
      | n :: r => let full := map low_cp (cps n) in
                  let k := if len3 then 3%nat else List.length full in
                  if prefix_of (firstn k full) (map low_cp s) then Some (i, skipn k s) else go (i + 1) r
      end in
  go 1 names.

Fixpoint std_aux (fuel : nat) (fmt s : list Z) (f : sfields) : option sfields :=
  match fuel with
  | O => None
  | S fu =>
    (* the spaces before a number are skipped *)
    let num k (set : Z -> sfields) (r : list Z) :=
        let fix skip (x : list Z) := match x with 32 :: x' => skip x' | _ => x end in
        match take_digits k (skip s) 0 0 with Some (v, _, s') => std_aux fu r s' (set v) | None => None end in
    let D := fun f => mk_sf (sf_y f) (sf_mo f) (sf_d f) (sf_h f) (sf_mi f) (sf_s f) (sf_us f) (sf_pm f) (sf_doy f) true (sf_time f) (sf_frac f) in
    let T := fun f => mk_sf (sf_y f) (sf_mo f) (sf_d f) (sf_h f) (sf_mi f) (sf_s f) (sf_us f) (sf_pm f) (sf_doy f) (sf_date f) true (sf_frac f) in
    match fmt with
    | nil => Some f
    | 37 :: c :: r =>
      if c =? 89 then num 4%nat (fun v => D (mk_sf (Some v) (sf_mo f) (sf_d f) (sf_h f) (sf_mi f) (sf_s f) (sf_us f) (sf_pm f) (sf_doy f) true (sf_time f) (sf_frac f))) r
      else if c =? 121 then num 2%nat (fun v => D (mk_sf (Some (if v <? 70 then 2000 + v else 1900 + v)) (sf_mo f) (sf_d f) (sf_h f) (sf_mi f) (sf_s f) (sf_us f) (sf_pm f) (sf_doy f) true (sf_time f) (sf_frac f))) r
      else if (c =? 109) || (c =? 99) then num 2%nat (fun v => D (mk_sf (sf_y f) (Some v) (sf_d f) (sf_h f) (sf_mi f) (sf_s f) (sf_us f) (sf_pm f) (sf_doy f) true (sf_time f) (sf_frac f))) r
      else if (c =? 100) || (c =? 101) then num 2%nat (fun v => D (mk_sf (sf_y f) (sf_mo f) (Some v) (sf_h f) (sf_mi f) (sf_s f) (sf_us f) (sf_pm f) (sf_doy f) true (sf_time f) (sf_frac f))) r
      else if (c =? 72) || (c =? 107) || (c =? 104) || (c =? 73) || (c =? 108) then num 2%nat (fun v => T (mk_sf (sf_y f) (sf_mo f) (sf_d f) v (sf_mi f) (sf_s f) (sf_us f) (sf_pm f) (sf_doy f) (sf_date f) true (sf_frac f))) r
      else if c =? 105 then num 2%nat (fun v => T (mk_sf (sf_y f) (sf_mo f) (sf_d f) (sf_h f) v (sf_s f) (sf_us f) (sf_pm f) (sf_doy f) (sf_date f) true (sf_frac f))) r
      else if (c =? 115) || (c =? 83) then num 2%nat (fun v => T (mk_sf (sf_y f) (sf_mo f) (sf_d f) (sf_h f) (sf_mi f) v (sf_us f) (sf_pm f) (sf_doy f) (sf_date f) true (sf_frac f))) r
      else if c =? 102 then
        match take_digits 6 s 0 0 with
        | Some (v, n, s') => std_aux fu r s' (mk_sf (sf_y f) (sf_mo f) (sf_d f) (sf_h f) (sf_mi f) (sf_s f) (v * 10 ^ (6 - Z.of_nat n)) (sf_pm f) (sf_doy f) (sf_date f) true true)
        | None => None end
      else if c =? 106 then num 3%nat (fun v => D (mk_sf (sf_y f) (sf_mo f) (sf_d f) (sf_h f) (sf_mi f) (sf_s f) (sf_us f) (sf_pm f) (Some v) true (sf_time f) (sf_frac f))) r
      else if c =? 112 then
        match map low_cp (firstn 2 s) with
        | [97; 109] => std_aux fu r (skipn 2 s) (mk_sf (sf_y f) (sf_mo f) (sf_d f) (sf_h f) (sf_mi f) (sf_s f) (sf_us f) (Some false) (sf_doy f) (sf_date f) true (sf_frac f))
        | [112; 109] => std_aux fu r (skipn 2 s) (mk_sf (sf_y f) (sf_mo f) (sf_d f) (sf_h f) (sf_mi f) (sf_s f) (sf_us f) (Some true) (sf_doy f) (sf_date f) true (sf_frac f))
        | _ => None end
      else if (c =? 77) || (c =? 98) then
        match name_match month_names (c =? 98) s with
        | Some (m, s') => std_aux fu r s' (D (mk_sf (sf_y f) (Some m) (sf_d f) (sf_h f) (sf_mi f) (sf_s f) (sf_us f) (sf_pm f) (sf_doy f) true (sf_time f) (sf_frac f)))
        | None => None end
      else if (c =? 87) || (c =? 97) then
        match name_match day_names (c =? 97) s with Some (_, s') => std_aux fu r s' f | None => None end
      else if c =? 84 then std_aux fu (cps "%H:%i:%s" ++ r) s f
      else if c =? 114 then std_aux fu (cps "%h:%i:%s %p" ++ r) s f
      else (match s with x :: s' => if x =? c then std_aux fu r s' f else None | nil => None end)
    | c :: r => match s with x :: s' => if x =? c then std_aux fu r s' f else None | nil => None end
    end
  end.

Definition my_str_to_date (s fmt : string) : value :=
  let fs := cps fmt in
  match std_aux (4 * S (List.length fs + String.length s)) fs (cps s) sf0 with
  | Some f =>
    let h := match sf_pm f with Some true => (if sf_h f =? 12 then 12 else sf_h f + 12)
                              | Some false => (if sf_h f =? 12 then 0 else sf_h f) | None => sf_h f end in
    let us := ((h * 60 + sf_mi f) * 60 + sf_s f) * usec_s + sf_us f in
    let fsp := if sf_frac f then 6%nat else 0%nat in
    if (59 <? sf_mi f) || (59 <? sf_s f) then Value_T None
    else if negb (sf_date f) then VTime us fsp
    else let days := match sf_y f, sf_doy f, sf_mo f, sf_d f with
                     | Some y, Some j, _, _ => if (0 <? j) && (j <=? (if is_leap y then 366 else 365)) then Some (days_from_civil y 1 1 + j - 1) else None
                     | Some y, None, Some m, Some d => if valid_date y m d then Some (days_from_civil y m d) else None
                     | _, _, _, _ => None
                     end in
         match days with
         | Some dd => if sf_time f then (if 23 <? h then Value_T None else VTs (ts_of dd us) fsp) else VDate dd
         | None => Value_T None
         end
  | None => Value_T None
  end.

(** * Other MySQL functions *)

(** [FROM_DAYS (n)]: the inverse of [TO_DAYS] (day 0 is [0000-00-00]; the days before year 1 give NULL) *)
Definition my_from_days (n : Z) : value := if n <? 366 then Value_T None else VDate (n - 719528).

(** [SEC_TO_TIME] and [TIME] values are bounded by [838:59:59] *)
Definition time_max : Z := (838 * 3600 + 59 * 60 + 59) * usec_s.
Definition clamp_time (us : Z) : Z := Z.max (- time_max) (Z.min time_max us).

(** [PERIOD_ADD (p, n)], [PERIOD_DIFF (p1, p2)]: periods [YYMM] or [YYYYMM] (a two-digit year below 70 is
    in 20xx) *)
Definition period_months (p : Z) : Z :=
  let y := p / 100 in let m := p mod 100 in
  let y := if y <? 70 then y + 2000 else if y <? 100 then y + 1900 else y in
  y * 12 + m - 1.
Definition months_period (n : Z) : Z := (n / 12) * 100 + n mod 12 + 1.

(** [TIME_FORMAT]: [DATE_FORMAT] of a time, where the hour can exceed 23 *)
Definition time_format (us : Z) (fmt : string) : string :=
  (* the hours of the day are taken modulo 24 by [my_format]: the format of a time uses the first day *)
  my_format (S (String.length fmt)) (ts_of 0 (Z.modulo us (24 * usec_h))) fmt.

(** [EXTRACT (unit FROM t)] of the MySQL family *)
Definition my_extract (unit : string) (ts : Z) : option Z :=
  let '(y, m, d) := civil_from_days (ts_days ts) in
  let us := ts_usec ts in
  let h := us / usec_h in let mi := (us / 60000000) mod 60 in let se := (us / usec_s) mod 60 in
  match unit with
  | "YEAR"%string => Some y | "QUARTER"%string => Some ((m + 2) / 3) | "MONTH"%string => Some m | "DAY"%string => Some d
  | "HOUR"%string => Some h | "MINUTE"%string => Some mi | "SECOND"%string => Some se | "MICROSECOND"%string => Some (us mod usec_s)
  | "YEAR_MONTH"%string => Some (y * 100 + m) | "DAY_HOUR"%string => Some (d * 100 + h)
  | "DAY_MINUTE"%string => Some ((d * 100 + h) * 100 + mi) | "DAY_SECOND"%string => Some (((d * 100 + h) * 100 + mi) * 100 + se)
  | "HOUR_MINUTE"%string => Some (h * 100 + mi) | "HOUR_SECOND"%string => Some ((h * 100 + mi) * 100 + se)
  | "MINUTE_SECOND"%string => Some (mi * 100 + se)
  (* the units [..._MICROSECOND]: the microseconds on 6 digits ([func_sapdb]) *)
  | "DAY_MICROSECOND"%string => Some ((((d * 100 + h) * 100 + mi) * 100 + se) * usec_s + us mod usec_s)
  | "HOUR_MICROSECOND"%string => Some (((h * 100 + mi) * 100 + se) * usec_s + us mod usec_s)
  | "MINUTE_MICROSECOND"%string => Some ((mi * 100 + se) * usec_s + us mod usec_s)
  | "SECOND_MICROSECOND"%string => Some (se * usec_s + us mod usec_s)
  | _ => None
  end.

(** * PostgreSQL *)

(** [age (a, b)]: years, months and days between [a] and [b], borrowing from the larger fields as
    [timestamp_age] does (a negative day count borrows the days of the month of the earlier date) *)
Definition pg_age (a b : Z) : value :=
  let neg := a <? b in
  let '(x, y) := if neg then (b, a) else (a, b) in
  let '(y1, m1, d1) := civil_from_days (ts_days x) in
  let '(y2, m2, d2) := civil_from_days (ts_days y) in
  let u1 := ts_usec x in let u2 := ts_usec y in
  let us := u1 - u2 in
  let '(d1, us) := if us <? 0 then (d1 - 1, us + 24 * usec_h) else (d1, us) in
  let dd := d1 - d2 in
  let '(m1, dd) := if dd <? 0 then
                     (* borrow the days of the month of the earlier date *)
                     (m1 - 1, dd + days_in_month y2 m2)
                   else (m1, dd) in
  let mo := (y1 - y2) * 12 + (m1 - m2) in
  if neg then VIntv (- mo) (- dd) (- us) else VIntv mo dd us.

(** [justify_days]: 30 days are a month; [justify_hours]: 24 hours are a day *)
Definition justify_days (mo d us : Z) : Z * Z * Z := (mo + Z.quot d 30, Z.rem d 30, us).
Definition justify_hours (mo d us : Z) : Z * Z * Z := (mo, d + Z.quot us (24 * usec_h), Z.rem us (24 * usec_h)).

(** [date_bin (stride, source, origin)]: the start of the bin of [stride] (without months) containing [source] *)
Definition date_bin (stride source origin : Z) : option Z :=
  if stride <=? 0 then None else Some (origin + Z.div (source - origin) stride * stride).

(** PostgreSQL [to_date] / [to_timestamp (text, format)]: the patterns [YYYY YY MM DD HH24 HH12 HH MI SS MS
    US Mon MON Month AM PM]; the other characters are skipped one for one *)
Fixpoint pg_parse (fuel : nat) (fmt s : list Z) (acc : Z * Z * Z * Z * Z * Z * Z * option bool) {struct fuel}
  : option (Z * Z * Z * Z * Z * Z * Z * option bool) :=
  match fuel with
  | O => None
  | S fu =>
    let '(y, mo, d, h, mi, se, us, pm) := acc in
    let up := map up_cp fmt in
    let num k p (set : Z -> nat -> Z * Z * Z * Z * Z * Z * Z * option bool) :=
        match take_digits k s 0 0 with
        | Some (v, n, s') => pg_parse fu (skipn (List.length (cps p)) fmt) s' (set v n)
        | None => None end in
    if prefix_of (cps "YYYY") up then num 4%nat "YYYY" (fun v _ => (v, mo, d, h, mi, se, us, pm))
    else if prefix_of (cps "HH24") up then num 2%nat "HH24" (fun v _ => (y, mo, d, v, mi, se, us, pm))
    else if prefix_of (cps "HH12") up then num 2%nat "HH12" (fun v _ => (y, mo, d, v, mi, se, us, pm))
    else if prefix_of (cps "MONTH") up then
      match name_match month_names false s with
      | Some (m, s') => pg_parse fu (skipn 5 fmt) s' (y, m, d, h, mi, se, us, pm) | None => None end
    else if prefix_of (cps "MON") up then
      match name_match month_names true s with
      | Some (m, s') => pg_parse fu (skipn 3 fmt) s' (y, m, d, h, mi, se, us, pm) | None => None end
    else if prefix_of (cps "YY") up then num 2%nat "YY" (fun v _ => (if v <? 70 then 2000 + v else 1900 + v, mo, d, h, mi, se, us, pm))
    else if prefix_of (cps "MM") up then num 2%nat "MM" (fun v _ => (y, v, d, h, mi, se, us, pm))
    else if prefix_of (cps "DD") up then num 2%nat "DD" (fun v _ => (y, mo, v, h, mi, se, us, pm))
    else if prefix_of (cps "HH") up then num 2%nat "HH" (fun v _ => (y, mo, d, v, mi, se, us, pm))
    else if prefix_of (cps "MI") up then num 2%nat "MI" (fun v _ => (y, mo, d, h, v, se, us, pm))
    else if prefix_of (cps "SS") up then num 2%nat "SS" (fun v _ => (y, mo, d, h, mi, v, us, pm))
    else if prefix_of (cps "MS") up then num 3%nat "MS" (fun v n => (y, mo, d, h, mi, se, v * 10 ^ (6 - Z.of_nat n), pm))
    else if prefix_of (cps "US") up then num 6%nat "US" (fun v n => (y, mo, d, h, mi, se, v * 10 ^ (6 - Z.of_nat n), pm))
    else if prefix_of (cps "AM") up || prefix_of (cps "PM") up then
      match map up_cp (firstn 2 s) with
      | [65; 77] => pg_parse fu (skipn 2 fmt) (skipn 2 s) (y, mo, d, h, mi, se, us, Some false)
      | [80; 77] => pg_parse fu (skipn 2 fmt) (skipn 2 s) (y, mo, d, h, mi, se, us, Some true)
      | _ => None end
    else match fmt, s with
         | nil, _ => Some acc
         | _ :: fr, _ :: sr => pg_parse fu fr sr acc
         | _ :: fr, nil => pg_parse fu fr nil acc
         end
  end.

Definition pg_to_timestamp (s fmt : string) : option Z :=
  match pg_parse (4 * S (String.length fmt + String.length s)) (cps fmt) (cps s) (1, 1, 1, 0, 0, 0, 0, None) with
  | Some (y, mo, d, h, mi, se, us, pm) =>
    let h := match pm with Some true => (if h =? 12 then 12 else h + 12) | Some false => (if h =? 12 then 0 else h) | None => h end in
    if valid_date y mo d && (h <? 24) && (mi <? 60) && (se <? 60)
    then Some (ts_of (days_from_civil y mo d) (((h * 60 + mi) * 60 + se) * usec_s + us)) else None
  | None => None
  end.

(** * Oracle [NEXT_DAY (d, 'MONDAY')], [TRUNC (d [, fmt])], [ROUND (d [, fmt])] for the formats [DD]
    (default), [MM]/[MONTH]/[MON], [YYYY]/[YEAR]/[YY], [HH]/[HH24], [MI] *)
Definition next_day (ts : Z) (name : string) : option Z :=
  match name_match day_names (Nat.leb (String.length name) 3) (cps name) with
  | Some (k, _) =>
    let dow := day_of_week (ts_days ts) in
    let delta := Z.modulo (k - 1 - dow) 7 in
    Some (ts_of (ts_days ts + (if delta =? 0 then 7 else delta)) (ts_usec ts))
  | None => None
  end.

Definition ora_trunc_round (round : bool) (ts : Z) (fmt : string) : option Z :=
  let days := ts_days ts in
  let us := ts_usec ts in
  let '(y, m, d) := civil_from_days days in
  match Temporal.upper_string fmt with
  | "DD"%string | "DDD"%string | "J"%string =>
    Some (ts_of (if round && (12 * usec_h <=? us) then days + 1 else days) 0)
  | "MM"%string | "MON"%string | "MONTH"%string | "RM"%string =>
    let first := days_from_civil y m 1 in
    Some (ts_of (if round && (16 <=? d) then add_months first 1 else first) 0)
  | "YYYY"%string | "YEAR"%string | "YY"%string | "Y"%string | "SYYYY"%string =>
    let first := days_from_civil y 1 1 in
    Some (ts_of (if round && (7 <=? m) then days_from_civil (y + 1) 1 1 else first) 0)
  | "HH"%string | "HH24"%string | "HH12"%string =>
    let h := us / usec_h in
    Some (ts_of days ((if round && (30 * 60000000 <=? us mod usec_h) then h + 1 else h) * usec_h))
  | "MI"%string =>
    let mi := us / 60000000 in
    Some (ts_of days ((if round && (30 * usec_s <=? us mod 60000000) then mi + 1 else mi) * 60000000))
  | _ => None
  end.
