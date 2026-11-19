(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**                            The SQLite dialect                                   *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String Ascii ZArith NArith QArith Qcanon.

Require Import Bool3 OrderedSet SqlFull IEEE Temporal Json Values Dialects ValueKit Collation PostgreSQL MySQL Hash StringFuns JsonFuns SystemFuns.

Close Scope Q_scope.
Close Scope Qc_scope.
Open Scope string_scope.
Open Scope Z_scope.

Import NullValues.
Import ListNotations.

(** * SQLite 3.4x

    - values are dynamically typed. Their order is: NULL, then the numbers (integers and
      reals, compared as numbers), then the strings; a string is never converted to
      compare it with a number. (The conversions of the _affinity_ of a column are not
      modelled: a literal is compared with a column as with any other value.)
    - there is no boolean type: [TRUE] and [FALSE] are 1 and 0, conditions are the
      integers 1, 0 and NULL; a value which is used as a condition is true when it is a
      non-zero number (strings are read as numbers);
    - strings are compared byte by byte ([BINARY]); [LIKE] is case insensitive for ASCII
      characters, and has no escape character unless [ESCAPE] is given;
    - NULLs are the smallest values of [ORDER BY];
    - [/] on two integers is the integer division, truncated towards zero, and a division
      by zero is NULL; [%] casts its operands to integers; [||] is the concatenation, and
      NULL if an operand is NULL; [CONCAT] ignores the NULLs;
    - the scalar [min] and [max] are NULL as soon as one argument is NULL;
    - [round] returns a real; [avg] is a real, [sum] is an integer if all its arguments
      are integers, [total] is a real and is 0 on an empty set.
    - bare columns of an aggregate query are read in the first row of the group.
    Integers are unbounded and reals are exact rationals: overflows and rounding are not
    modelled. *)

(** the collation of a comparison: the explicit collation of the left operand, otherwise of the right
    one, otherwise [BINARY] ("Rules for determining which collating function to use", datatype3.html) *)
Definition lite_coll (v : value) : option (collation * bool) :=
  match v with Value_C (Some (_, n)) => lite_collation_of_name n | _ => None end.

Definition lite_str (v : value) : option string :=
  match v with Value_string (Some s) => Some s | Value_C (Some (s, _)) => Some s | _ => None end.

Definition lite_compare (v1 v2 : value) : option comparison :=
  if (is_null v1 || is_null v2)%bool then None
  else match lite_str v1, lite_str v2 with
       | Some a, Some b => 
         let (c, p) := match lite_coll v1, lite_coll v2 with
                       | Some cp, _ | None, Some cp => cp
                       | None, None => (Coll_Binary, false) end in
         Some (string_compare (Collation.coll_key c p a) (Collation.coll_key c p b))
       | Some _, None => Some Gt
       | None, Some _ => Some Lt
       | _, _ =>
    match lenient v1, lenient v2 with
    | Some a, Some b => Some (num_cmp a b)
    | _, _ => None
    end
  end.

Definition lite_order (a b : value) : comparison :=
  match lite_compare a b with Some c => c | None => value_compare a b end.

Definition lite_truth := my_truth.
Definition lite_of_truth := my_of_truth.

Definition lite_eq3 (a b : value) : bool3 := cmp_pred lite_compare is_Eq (a :: b :: nil).

Definition lite_null_safe_eq (a b : value) : bool3 :=
  match is_null a, is_null b with
  | true, true => true3
  | false, false => lite_eq3 a b
  | _, _ => false3
  end.

Definition lite_like (v p : value) : bool3 :=
  match text_of v, text_of p with
  | Some s, Some p => bool3_of_bool (like_gen None (lower_s p) (lower_s s))
  | _, _ => unknown3
  end.

Definition lite_pred_table : list (string * (list value -> bool3)) :=
  comparison_table lite_compare ++
  ("is", binary3 lite_null_safe_eq)
  :: ("is not", binary3 (fun a b => negb3 (lite_null_safe_eq a b)))
  :: ("is distinct from", binary3 (fun a b => negb3 (lite_null_safe_eq a b)))
  :: ("is not distinct from", binary3 lite_null_safe_eq)
  :: ("is null", unary3 (fun v => bool3_of_bool (is_null v)))
  :: ("is not null", unary3 (fun v => bool3_of_bool (negb (is_null v))))
  :: ("is true", unary3 (truth_is true3))
  :: ("is not true", unary3 (fun v => negb3 (truth_is true3 v)))
  :: ("is false", unary3 (truth_is false3))
  :: ("is not false", unary3 (fun v => negb3 (truth_is false3 v)))
  :: ("like", binary3 lite_like)
  :: ("not like", binary3 (fun v p => negb3 (lite_like v p)))
  :: nil.

(** [substr(s, start, len)]: 1-based; a negative start counts from the end; a negative
    length takes the characters which precede [start]; position 0 is before the first
    character. *)
Definition lite_substr (s : string) (start : Z) (len : option Z) : string :=
  let total := Z.of_nat (String.length s) in
  let st := if (Z.ltb start 0) then total + start + 1 else start in
  let '(a, b) := match len with
                 | None => (st, total + 1)
                 | Some l => if (Z.leb 0 l) then (st, st + l) else (st + l, st)
                 end in
  let a' := Z.max a 1 in
  let b' := Z.min b (total + 1) in
  if (Z.leb b' a') then EmptyString 
  else String.substring (Z.to_nat (a' - 1)) (Z.to_nat (b' - a')) s.

Definition lite_substr_fun (l : list value) : value :=
  match l with
  | s :: p :: nil => match text_of s, z_arg p with
                     | Some s, Some p => Value_string (Some (lite_substr s p None))
                     | _, _ => Value_string None end
  | s :: p :: n :: nil => match text_of s, z_arg p, z_arg n with
                          | Some s, Some p, Some n => Value_string (Some (lite_substr s p (Some n)))
                          | _, _, _ => Value_string None end
  | _ => Value_string None
  end.

Definition lite_div (a b : num) : option num :=
  match a, b with
  | Num_Z _, Num_Z _ => num_div_trunc a b
  | _, _ => num_div_exact a b
  end.

(** [%] casts its operands to integers; the result is a real if one of them is. *)
Definition lite_mod (a b : num) : option num :=
  let toz n := match n with Num_Z z => z | Num_Q q => Qc_trunc q end in
  let x := toz a in let y := toz b in
  if (Z.eqb y 0) then None 
  else match a, b with
       | Num_Z _, Num_Z _ => Some (Num_Z (Z.rem x y))
       | _, _ => Some (Num_Q (Qc_of_Z (Z.rem x y)))
       end.

Definition type_name (v : value) : string :=
  match v with
  | Value_Z (Some _) | Value_bool (Some _) => "integer"
  | Value_Q (Some _) | Value_F (Some _) => "real"
  | Value_string (Some _) => "text"
  | _ => "null"
  end.

Definition lite_concat (l : list value) : value :=
  if existsb is_null l then Value_string None
  else Value_string (Some (fold_left (fun acc v => match text_of v with Some s => acc ++ s | None => acc end) l EmptyString)).

(** [concat] and [concat_ws] ignore the NULLs *)
Definition lite_concat_skip (l : list value) : value :=
  Value_string (Some (fold_left (fun acc v => match text_of v with Some s => acc ++ s | None => acc end) l EmptyString)).

(** * Dates and times ([src/date.c])

    SQLite has no date type: the date functions read a time value (a text [YYYY-MM-DD], [YYYY-MM-DD HH:MM[:SS[.SSS]]],
    [HH:MM[:SS]], ['now'], or a number of the Julian day), apply the modifiers in order, and return a text.
    A month or a year modifier does not clamp the day: the date is normalized ([2024-01-31] + 1 month is
    [2024-03-02]). An invalid time value or modifier gives NULL. *)
Definition lite_time_value (v : value) : option Z :=
  match v with
  | Value_string (Some t) =>
    if String.eqb t "now" then Some statement_time
    else match parse_timestamp t with
         | Some x => Some x
         | None => match parse_time (if Nat.eqb (String.length t) 5 then t ++ ":00" else t) with
                   | Some u => Some (ts_of (days_from_civil 2000 1 1) u)
                   | None => match split_at " " t with
                             | [d; hm] => match parse_date d, parse_time (hm ++ ":00") with
                                          | Some dd, Some u => Some (ts_of dd u) | _, _ => None end
                             | _ => None end
                   end
         end
  | _ => match lenient v with
         (* a number is a Julian day *)
         | Some n => let q := Qc_of_num n in
                     Some (Qc_round (Qcmult (Qcminus q (Q2Qc (Qmake 4881175 2))) (Qc_of_Z usec_per_day)))
         | None => None
         end
  end.

Definition lite_modifier (t : Z) (m : string) : option Z :=
  let w := filter (fun x => negb (String.eqb x EmptyString)) (split_at " " m) in
  let shift (n : Z) (unit : string) : option Z :=
      match unit with
      | "day" | "days" => Some (t + n * usec_per_day)
      | "hour" | "hours" => Some (t + n * 3600000000)
      | "minute" | "minutes" => Some (t + n * 60000000)
      | "second" | "seconds" => Some (t + n * 1000000)
      | "month" | "months" | "year" | "years" =>
        let k := if (String.eqb unit "month" || String.eqb unit "months")%bool then n else n * 12 in
        let '(y, mo, d) := civil_from_days (ts_days t) in
        let tot := y * 12 + (mo - 1) + k in
        Some (ts_of (days_from_civil (tot / 12) (tot mod 12 + 1) d) (ts_usec t))
      | _ => None
      end%string in
  match w with
  | ["weekday"; n] => match Z_of_string n with
                      | Some k => let d := ts_days t in Some (ts_of (d + (k - day_of_week d) mod 7) (ts_usec t))
                      | None => None end
  | [n; unit] => 
    let n' := match n with String "+" r => r | _ => n end in
    match Z_of_string n' with Some k => shift k unit | None => None end
  | ["start"; "of"; "day"] => Some (ts_of (ts_days t) 0)
  | ["start"; "of"; "month"] => let '(y, mo, _) := civil_from_days (ts_days t) in Some (ts_of (days_from_civil y mo 1) 0)
  | ["start"; "of"; "year"] => let '(y, _, _) := civil_from_days (ts_days t) in Some (ts_of (days_from_civil y 1 1) 0)
  | ["utc"] | ["localtime"] => Some t
  | _ => None
  end%string.

Definition lite_eval_time (l : list value) : option Z :=
  match l with
  | nil => Some statement_time
  | v :: mods =>
    if existsb is_null l then None else
    match lite_time_value v with
    | Some t => fold_left (fun acc m => match acc, text_of m with Some t, Some m => lite_modifier t m | _, _ => None end) mods (Some t)
    | None => None
    end
  end.

Definition lite_hms (u : Z) : string := time_text u 0.

(** [strftime]: [%d %f %H %j %J %m %M %s %S %w %Y %%] *)
Fixpoint lite_strftime (fuel : nat) (t : Z) (fmt : string) : string :=
  match fuel with
  | O => EmptyString
  | S f =>
    match fmt with
    | EmptyString => EmptyString
    | String "%" (String c r) =>
      let days := ts_days t in
      let '(y, m, d) := civil_from_days days in
      let us := ts_usec t in
      let piece :=
          match c with
          | "d" => pad 2 d | "m" => pad 2 m | "Y" => pad 4 y | "H" => pad 2 (us / 3600000000)
          | "M" => pad 2 ((us / 60000000) mod 60) | "S" => pad 2 ((us / 1000000) mod 60)
          | "f" => (pad 2 ((us / 1000000) mod 60) ++ "." ++ pad 3 ((us / 1000) mod 1000))%string
          | "j" => pad 3 (day_of_year days) | "w" => NullValues.string_of_Z (day_of_week days)
          | "s" => NullValues.string_of_Z (Z.div t 1000000)
          | "%" => "%"%string
          | _ => String "%" (String c EmptyString)
          end%char in
      piece ++ lite_strftime f t r
    | String c r => String c (lite_strftime f t r)
    end
  end.

(** * JSON ([src/json.c])

    SQLite has no JSON type: the JSON functions return texts (minified, the members in their order), and
    [json_extract] and [->>] return SQL values (a string, an integer, a real, 1 or 0 for [true] and
    [false], NULL for [null], the text of an array or an object). An argument which is not valid JSON is an
    error ([malformed JSON]). The subtype which marks a text as JSON is not modelled: a text given to
    [json_array] or [json_object] is a JSON string. *)
Definition lite_json_doc (v : value) : option (option json) :=
  if is_null v then Some None
  else match text_of v with
       | Some t => match parse_json t with Some j => Some (Some j) | None => None end
       | None => Some None
       end.

Definition lite_json_of_value (v : value) : json :=
  if is_null v then JNull else
  match v with
  | Value_Z (Some z) => JNum (NullValues.string_of_Z z)
  | Value_F (Some (x, k)) => JNum (lite_text (special_of_tag (Nat.div (Nat.modulo k 10) 2)) x)
  | _ => match text_of v with Some t => JStr t | None => JNull end
  end.

Definition lite_sql_of_json (j : json) : value :=
  match j with
  | JNull => Value_Z None
  | JBool b => Value_Z (Some (if b then 1 else 0))
  | JStr t => Value_string (Some t)
  | JNum t => match Z_of_string t with Some z => Value_Z (Some z) | None => to_float false (Qc_of_num (parse_prefix t)) end
  | _ => Value_string (Some (text_compact j))
  end.

Definition lite_json_type (j : json) : string :=
  match j with
  | JNull => "null" | JBool true => "true" | JBool false => "false"
  | JNum t => match Z_of_string t with Some _ => "integer" | None => "real" end
  | JStr _ => "text" | JArr _ => "array" | JObj _ => "object"
  end.

Definition lite_json_at (doc p : value) : option (option json) :=
  match lite_json_doc doc, text_of p with
  | None, _ => None
  | Some None, _ => Some None
  | Some (Some d), Some path => match parse_path path with Some st => Some (follow st d) | None => None end
  | _, None => Some None
  end.

(** the text of an argument of a string function: a [REAL] is written with ["%!.15g"] *)
Definition lite_skit : skit :=
  mk_skit (fun v => match v with
                    | Value_F (Some (x, k)) => Some (lite_text (special_of_tag (Nat.div (Nat.modulo k 10) 2)) x)
                    | Value_C (Some (s, _)) => Some s
                    | _ => text_of v end)
          (fun v => match lenient v with Some (Num_Z z) => Some z | Some (Num_Q q) => Some (Qc_trunc q) | None => None end)
          (fun s => Value_string (Some s)) (Value_string None).

(** [json_set (doc, path, value, ...)] and its kin: a text value is a JSON string *)
Definition lite_json_update (create replace : bool) (l : list value) : value :=
  match l with
  | d :: rest =>
    match lite_json_doc d with
    | Some (Some j) =>
      let fix go (r : list value) (acc : json) : option json :=
          match r with
          | nil => Some acc
          | p :: v :: r' => match text_of p with
                            | Some t => match parse_path t with
                                        | Some st => go r' (set_path create replace st acc (lite_json_of_value v))
                                        | None => None end
                            | None => go r' acc end
          | _ => None
          end in
      match go rest j with Some r => Value_string (Some (text_compact r)) | None => Value_Err "bad JSON path" end
    | Some None => Value_string None
    | None => Value_Err "malformed JSON"
    end
  | nil => Value_Err "wrong number of arguments"
  end.

Definition lite_symbol_table_raw : list (string * (list value -> value)) :=
  let conv := lenient in
  let plus := num_fun2 conv (fun a b => Some (num_plus a b)) in
  let minus := num_fun2 conv (fun a b => Some (num_minus a b)) in
  let mult := num_fun2 conv (fun a b => Some (num_mult a b)) in
  let opp := num_fun1 conv num_opp in
  let div := num_fun2 conv lite_div in
  let modulo := num_fun2 conv lite_mod in
  let logic_and := fun l => lite_of_truth (fold_truth lite_truth andb3 true3 l) in
  let logic_or := fun l => lite_of_truth (fold_truth lite_truth orb3 false3 l) in
     ("plus", plus) :: ("+", plus)
  :: ("minus", minus) :: ("-", minus)
  :: ("mult", mult) :: ("*", mult)
  :: ("opp", opp) :: ("neg", opp)
  :: ("/", div) :: ("div", div)
  :: ("%", modulo) :: ("mod", modulo)
  :: ("abs", num_fun1 conv num_abs)
  :: ("sign", num_fun1 conv num_sign)
  :: ("round", fun l => match l with
                        | v :: nil => match conv v with 
                                      | Some a => Value_Q (Some (Qc_of_num (num_round a 0))) 
                                      | None => Value_Q None end
                        | v :: d :: nil => match conv v, z_arg d with
                                           | Some a, Some d => Value_Q (Some (Qc_of_num (num_round a d))) 
                                           | _, _ => Value_Q None end
                        | _ => Value_Q None end)
  :: ("power", num_fun2 conv num_power) :: ("pow", num_fun2 conv num_power)
  (* scalar min and max *)
  :: ("min", extremum_strict is_null lite_order is_Lt)
  :: ("max", extremum_strict is_null lite_order is_Gt)
  (* conditional expressions *)
  :: ("coalesce", coalesce)
  :: ("ifnull", coalesce)
  :: ("iif", fun l => match l with 
                      | c :: a :: b :: nil => match lite_truth c with true3 => a | _ => b end
                      | _ => Value_Z None end)
  :: ("nullif", fun l => match l with
                         | v1 :: v2 :: nil => match lite_eq3 v1 v2 with
                                              | true3 => default_value (type_of_value v1)
                                              | _ => v1 end
                         | _ => Value_Z None end)
  :: ("case", case_by lite_truth)
  (* JSON *)
  :: ("json", fun l => match l with v :: nil => match lite_json_doc v with Some (Some j) => Value_string (Some (text_compact j)) | Some None => Value_string None | None => Value_Err "malformed JSON" end | _ => Value_string None end)
  :: ("json_extract", fun l => match l with d :: p :: nil => match lite_json_at d p with Some (Some r) => lite_sql_of_json r | Some None => Value_Z None | None => Value_Err "malformed JSON" end | _ => Value_Z None end)
  :: ("->", fun l => match l with d :: p :: nil => match lite_json_at d p with Some (Some r) => Value_string (Some (text_compact r)) | Some None => Value_string None | None => Value_Err "malformed JSON" end | _ => Value_string None end)
  :: ("->>", fun l => match l with d :: p :: nil => match lite_json_at d p with Some (Some r) => lite_sql_of_json r | Some None => Value_Z None | None => Value_Err "malformed JSON" end | _ => Value_Z None end)
  :: ("json_array", fun l => Value_string (Some (text_compact (JArr (map lite_json_of_value l)))))
  (* TODO 2.8: [json_set], [json_insert], [json_replace], [json_remove], [json_patch], [json_quote] *)
  :: ("json_set", lite_json_update true true) :: ("json_insert", lite_json_update true false)
  :: ("json_replace", lite_json_update false true)
  :: ("json_remove", fun l => match l with
                              | d :: paths => match lite_json_doc d with
                                              | Some (Some j) =>
                                                match fold_left (fun acc p => match acc, text_of p with
                                                                              | Some a, Some t => match parse_path t with Some st => Some (remove_path st a) | None => None end
                                                                              | Some a, None => Some a
                                                                              | None, _ => None end) paths (Some j) with
                                                | Some r => Value_string (Some (text_compact r))
                                                | None => Value_Err "bad JSON path" end
                                              | Some None => Value_string None
                                              | None => Value_Err "malformed JSON" end
                              | nil => Value_Err "wrong number of arguments" end)
  :: ("json_patch", fun l => match l with
                             | a :: b :: nil => match lite_json_doc a, lite_json_doc b with
                                                | Some (Some x), Some (Some y) => Value_string (Some (text_compact (merge_patch (json_size x + json_size y) x y)))
                                                | Some None, _ | _, Some None => Value_string None
                                                | _, _ => Value_Err "malformed JSON" end
                             | _ => Value_Err "wrong number of arguments" end)
  :: ("json_quote", fun l => match l with v :: nil => Value_string (Some (text_compact (lite_json_of_value v))) | _ => Value_Err "wrong number of arguments" end)
  :: ("json_object", fun l => 
        let fix pairs (l : list value) : option (list (string * json)) :=
            match l with
            | nil => Some nil
            | k :: v :: r => match text_of k, pairs r with Some key, Some rest => Some ((key, lite_json_of_value v) :: rest) | _, _ => None end
            | _ => None end in
        match pairs l with Some ps => Value_string (Some (text_compact (JObj ps))) | None => Value_Err "json_object() requires an even number of arguments" end)
  :: ("json_type", fun l => match l with 
                            | v :: nil => match lite_json_doc v with Some (Some j) => Value_string (Some (lite_json_type j)) | Some None => Value_string None | None => Value_Err "malformed JSON" end
                            | d :: p :: nil => match lite_json_at d p with Some (Some j) => Value_string (Some (lite_json_type j)) | Some None => Value_string None | None => Value_Err "malformed JSON" end
                            | _ => Value_string None end)
  :: ("json_valid", fun l => match l with v :: nil => if is_null v then Value_Z None else Value_Z (Some (match lite_json_doc v with Some (Some _) => 1 | _ => 0 end)) | _ => Value_Z None end)
  :: ("json_array_length", fun l => match l with 
                                    | v :: nil => match lite_json_doc v with Some (Some (JArr a)) => Value_Z (Some (Z.of_nat (List.length a))) | Some (Some _) => Value_Z (Some 0) | Some None => Value_Z None | None => Value_Err "malformed JSON" end
                                    | d :: p :: nil => match lite_json_at d p with Some (Some (JArr a)) => Value_Z (Some (Z.of_nat (List.length a))) | Some (Some _) => Value_Z (Some 0) | Some None => Value_Z None | None => Value_Err "malformed JSON" end
                                    | _ => Value_Z None end)
  :: ("date", fun l => match lite_eval_time l with Some t => Value_string (Some (date_text (ts_days t))) | None => Value_string None end)
  :: ("time", fun l => match lite_eval_time l with Some t => Value_string (Some (lite_hms (ts_usec t))) | None => Value_string None end)
  :: ("datetime", fun l => match lite_eval_time l with 
                           | Some t => Value_string (Some (date_text (ts_days t) ++ " " ++ lite_hms (ts_usec t))) 
                           | None => Value_string None end)
  :: ("julianday", fun l => match lite_eval_time l with 
                            | Some t => to_float false (Qcplus (Q2Qc (Qmake 4881175 2)) (Qcdiv (Qc_of_Z t) (Qc_of_Z usec_per_day)))
                            | None => Value_F None end)
  :: ("unixepoch", fun l => match lite_eval_time l with Some t => Value_Z (Some (Z.div t 1000000)) | None => Value_Z None end)
  :: ("strftime", fun l => match l with
                           | f :: r => match text_of f, lite_eval_time r with
                                       | Some fmt, Some t => Value_string (Some (lite_strftime (S (String.length fmt)) t fmt))
                                       | _, _ => Value_string None end
                           | _ => Value_string None end)
  (* [x COLLATE c]: [no such collation sequence] for an unknown name *)
  :: ("collate", fun l => match l with
                          | v :: Value_string (Some n) :: nil =>
                            match lite_collation_of_name n, text_of v with
                            | Some _, Some s => Value_C (Some (s, n))
                            | Some _, None => v
                            | None, _ => Value_Err "no such collation sequence"
                            end
                          | _ => Value_string None end)
  :: ("typeof", fun l => match l with v :: nil => Value_string (Some (type_name v)) | _ => Value_string None end)
  (* logic *)
  :: ("and", logic_and) :: ("or", logic_or)
  :: ("not", fun l => match l with v :: nil => lite_of_truth (negb3 (lite_truth v)) | _ => Value_Z None end)
  (* strings *)
  :: ("||", lite_concat)
  :: ("concat", lite_concat_skip)
  (* [length] of a text counts its characters ([lengthFunc]) *)
  :: ("length", str1 (fun s => Value_Z (Some (char_count s))))
  :: ("upper", str_fun1 upper_s) :: ("lower", str_fun1 lower_s)
  (* [trim (s, chars)]: a set of characters, a space by default ([trimFunc]) *)
  :: ("trim", f_trim_set lite_skit 0) :: ("ltrim", f_trim_set lite_skit 1) :: ("rtrim", f_trim_set lite_skit 2)
  :: ("trim_both", f_trim_set lite_skit 0) :: ("trim_leading", f_trim_set lite_skit 1) :: ("trim_trailing", f_trim_set lite_skit 2)
  :: ("substr", lite_substr_fun) :: ("substring", lite_substr_fun)
  :: ("concat_ws", f_concat_ws lite_skit)
  (* the scalar [max (a, b, ...)] and [min]: NULL if an argument is NULL; compared as by [ORDER BY]
     ([minmaxFunc]) *)
  :: ("max_scalar", fun l => if existsb is_null l then Value_Z None
                             else match l with v :: r => fold_left (fun a b => match lite_order a b with Lt => b | _ => a end) r v
                                          | nil => Value_Z None end)
  :: ("min_scalar", fun l => if existsb is_null l then Value_Z None
                             else match l with v :: r => fold_left (fun a b => match lite_order a b with Gt => b | _ => a end) r v
                                          | nil => Value_Z None end)
  (* hints to the planner: the value of the argument *)
  :: ("likely", fun l => match l with v :: nil => v | _ => Value_Err "wrong number of arguments" end)
  :: ("unlikely", fun l => match l with v :: nil => v | _ => Value_Err "wrong number of arguments" end)
  :: ("likelihood", fun l => match l with v :: _ :: nil => v | _ => Value_Err "wrong number of arguments" end)
  :: ("octet_length", str1 (fun s => Value_Z (Some (Z.of_nat (String.length s)))))
  (* [hex] of the text of the value (NULL gives ['']), in upper case; [unhex] NULL if not hexadecimal *)
  :: ("hex", fun l => match l with
                      | v :: nil => Value_string (Some (match sk_txt lite_skit v with
                                                        | Some s => hex_of_bytes true (bytes_of_string s)
                                                        | None => EmptyString end))
                      | _ => Value_Err "wrong number of arguments" end)
  :: ("unhex", fun l => match texts lite_skit l with
                        | Some (s :: nil) => match bytes_of_hex s with
                                             | Some b => if Nat.odd (String.length s) then Value_string None
                                                         else Value_string (Some (string_of_bytes b))
                                             | None => Value_string None end
                        | _ => Value_string None end)
  :: ("char", fun l => Value_string (Some (txt (flat_map (fun v => match sk_int lite_skit v with Some n => n :: nil | None => nil end) l))))
  :: ("unicode", fun l => match texts lite_skit l with
                          | Some (s :: nil) => match cps s with c :: _ => Value_Z (Some c) | nil => Value_Z None end
                          | _ => Value_Z None end)
  (* [quote]: a text between quotes (doubled inside), a number as its text, NULL as [NULL] *)
  :: ("quote", fun l => match l with
                        | (Value_string (Some s) | Value_C (Some (s, _))) :: nil =>
                          Value_string (Some (txt (39 :: flat_map (fun c => if Z.eqb c 39 then 39 :: 39 :: nil else c :: nil) (cps s) ++ 39 :: nil)))
                        | v :: nil => if is_null v then Value_string (Some "NULL"%string)
                                      else match sk_txt lite_skit v with Some t => Value_string (Some t) | None => Value_string None end
                        | _ => Value_Err "wrong number of arguments" end)
  :: ("replace", fun l => match l with
                          | s :: f :: t :: nil => match text_of s, text_of f, text_of t with
                                                  | Some s, Some f, Some t => Value_string (Some (string_replace s f t))
                                                  | _, _, _ => Value_string None end
                          | _ => Value_string None end)
  (* [instr] counts characters *)
  :: ("instr", fun l => match l with
                        | s :: sub :: nil => match sk_txt lite_skit s, sk_txt lite_skit sub with
                                             | Some s, Some sub => Value_Z (Some (strpos_cp (cps sub) (cps s)))
                                             | _, _ => Value_Z None end
                        | _ => Value_Z None end)
  (* casts *)
  :: ("cast_int", fun l => match l with 
                           | v :: nil => match lenient v with
                                         | Some (Num_Z z) => Value_Z (Some z)
                                         | Some (Num_Q q) => Value_Z (Some (Qc_trunc q))
                                         | None => Value_Z None end
                           | _ => Value_Z None end)
  :: ("cast_numeric", fun l => match l with
                               | v :: nil => match lenient v with Some n => value_of_num n | None => Value_Z None end
                               | _ => Value_Z None end)
  :: ("cast_real", fun l => match l with
                            | v :: nil => match lenient v with Some n => Value_Q (Some (Qc_of_num n)) | None => Value_Q None end
                            | _ => Value_Q None end)
  :: ("cast_string", fun l => match l with v :: nil => Value_string (text_of v) | _ => Value_string None end)
  :: nil.

Definition lite_aggregate_table_raw : list (string * (list value -> value)) :=
     ("count", agg_count_by is_null)
  :: ("count(*)", fun l => Value_Z (Some (Z.of_nat (List.length l))))
  (* [json_group_array (v)], [json_group_object (k, v)] *)
  :: ("json_group_array", fun l => Value_string (Some (text_compact (JArr (map lite_json_of_value l)))))
  :: ("json_group_object", fun l =>
        let fix pairs (r : list value) : list (string * json) :=
            match r with k :: v :: r' => match text_of k with Some t => (t, lite_json_of_value v) :: pairs r' | None => pairs r' end | _ => nil end in
        Value_string (Some (text_compact (JObj (pairs l)))))
  :: ("sum", agg_sum_by is_null lenient)
  :: ("total", fun l => match agg_sum_by is_null lenient l with
                        | Value_Z None => Value_Q (Some (Qc_of_Z 0))
                        | v => match lenient v with Some n => Value_Q (Some (Qc_of_num n)) | None => v end
                        end)
  :: ("avg", agg_avg_by is_null lenient)
  :: ("min", agg_extremum_by is_null lite_order is_Lt)
  :: ("max", agg_extremum_by is_null lite_order is_Gt)
  :: ("group_concat", agg_concat_by is_null ",")
  :: ("group_concat_sep", agg_concat_sep_by is_null ",")
  :: ("string_agg_sep", agg_concat_sep_by is_null ",")
  :: nil.

(** The constructs of SQLite 3.39 and later: no [LATERAL], no [INTERSECT ALL] nor 
    [EXCEPT ALL], no [ANY] and [ALL] subqueries. *)
(** * REAL

    A number of SQLite which is not an integer is a [REAL], a binary64 float: every result of an
    arithmetic function which is not an integer is the nearest double of the exact result (a
    correctly rounded operation). A [REAL] is printed with ["%!.15g"] ([lite_text]): the functions
    on texts see that text. *)
Definition lite_real (v : value) : value :=
  match v with
  (* an integer result which overflows 64 bits is a [REAL] ([sqlite3AddInt64] fails) *)
  | Value_Z (Some z) => if int_range_ok 64 z then v else to_float false (Qc_of_Z z)
  | Value_Q (Some q) => to_float false q
  | Value_Q None => Value_F None
  | Value_D (Some (q, _, _)) => to_float false q
  | _ => v
  end.

Definition lite_textual (l : list value) : list value :=
  map (fun v => match v with
                | Value_F (Some (x, k)) => Value_string (Some (lite_text (special_of_tag (Nat.div (Nat.modulo k 10) 2)) x))
                | _ => v
                end) l.

Definition lite_text_funs : list string :=
  "||" :: "concat" :: "length" :: "upper" :: "lower" :: "substr" :: "substring"
       :: "replace" :: "cast_string" :: nil.

Definition lite_symbol_table : list (string * (list value -> value)) :=
  map (fun p => if existsb (String.eqb (fst p)) lite_text_funs
                then (fst p, fun l => (snd p) (lite_textual l))
                else (fst p, fun l => lite_real ((snd p) l))) (sys_table default_env "SQLite" ++ c_math_table true lenient ++ bit_table true lenient ++ lite_round_table lenient ++ lite_symbol_table_raw).

Definition lite_aggregate_table : list (string * (list value -> value)) :=
  map (fun p => if existsb (String.eqb (fst p)) ("group_concat" :: "group_concat_sep" :: "string_agg_sep" :: nil)
                then (fst p, fun l => (snd p) (lite_textual l))
                (* [sum] of integers which overflows is an error ([integer overflow], [sumStep]); [total] is a REAL *)
                else if String.eqb (fst p) "sum"
                then (fst p, fun l => match (snd p) l with
                                      | Value_Z (Some z) => if int_range_ok 64 z then Value_Z (Some z) else Value_Err "integer overflow"
                                      | r => lite_real r end)
                else (fst p, fun l => lite_real ((snd p) l))) lite_aggregate_table_raw.

Definition lite_supports (f : feature) : bool :=
  match f with
  | F_Lateral | F_Intersect_All | F_Except_All | F_Any_All 
  | F_Grouping_Sets | F_Rollup | F_Cube | F_Fetch_Ties | F_Fetch_Percent => false
  | _ => true
  end.

Definition canon_lite (v : value) : value :=
  match v with
  | Value_C (Some (s, n)) => 
    Value_string (Some (match lite_collation_of_name n with Some (c, p) => Collation.coll_key c p s | None => s end))
  | Value_bool (Some b) => Value_Q (Some (Qc_of_Z (if b then 1 else 0)))
  | _ => canon_numeric v
  end.

(** * Type affinity ("Type Conversions Prior To Comparison", datatype3.html)

    When an operand of a comparison has [INTEGER], [REAL] or [NUMERIC] affinity and the other one [TEXT] or
    none, [NUMERIC] affinity is applied to the other one: a text which is a well-formed number becomes that
    number. When an operand has [TEXT] affinity and the other none, [TEXT] affinity is applied to the other
    one: a number becomes its text. A column has the affinity of its declared type; the other expressions
    have none. *)
Definition lite_numeric_affinity (v : value) : value :=
  match v with
  | Value_string (Some s) =>
    let t := string_rtrim (string_ltrim s) in
    match parse_number t with
    | (Num_Z z, true) => Value_Z (Some z)
    | (n, true) => to_float false (Qc_of_num n)
    | _ => v end
  | _ => v
  end.

Definition lite_text_affinity (v : value) : value :=
  match v with
  | Value_Z (Some z) => Value_string (Some (NullValues.string_of_Z z))
  | Value_F (Some (x, k)) => Value_string (Some (lite_text (special_of_tag (Nat.div (Nat.modulo k 10) 2)) x))
  | _ => v
  end.

Definition lite_comparisons : list string :=
  "=" :: "==" :: "<>" :: "!=" :: "<" :: "<=" :: ">" :: ">=" :: "is" :: "is not" :: "between" :: "not between" :: nil.

Definition lite_cmp_coerce (p : string) (ks : list nat) (l : list value) : list value :=
  if negb (existsb (String.eqb p) lite_comparisons) then l else
  match ks, l with
  | k1 :: k2 :: kr, v1 :: v2 :: vr =>
    let (v1', v2') :=
        if Nat.eqb k1 2 && negb (Nat.eqb k2 2) then (v1, lite_numeric_affinity v2)
        else if Nat.eqb k2 2 && negb (Nat.eqb k1 2) then (lite_numeric_affinity v1, v2)
        else if Nat.eqb k1 1 && Nat.eqb k2 0 then (v1, lite_text_affinity v2)
        else if Nat.eqb k2 1 && Nat.eqb k1 0 then (lite_text_affinity v1, v2)
        else (v1, v2) in
    v1' :: v2' :: vr
  | _, _ => l
  end.

Definition SQLite : vsem :=
  mk_vsem "SQLite"
          (table_of_list (like_table lite_skit false low_cp low_cp None
                          (* [REGEXP] calls the user function [regexp ()], which SQLite does not define *)
                          ++ ("regexp", fun _ => unknown3) :: ("not regexp", fun _ => unknown3) :: lite_pred_table))
          (table_of_list lite_symbol_table)
          (table_of_list lite_aggregate_table)
          is_null
          lite_truth
          lite_of_truth
          lite_eq3
          lite_order
          canon_lite
          true
          lite_supports
          true
          (* [ESCAPE expression must be a single character] *)
          (fun p l => bad_escape lite_skit p l || String.eqb p "regexp" || String.eqb p "not regexp")
          (* a literal with a decimal point is a [REAL] *)
          lite_real
          (fun _ => false)
          lite_cmp_coerce.
