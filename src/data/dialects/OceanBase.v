(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**                   The OceanBase dialects (MySQL and Oracle modes)               *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String Ascii ZArith NArith QArith Qcanon.

Require Import Collation Bool3 OrderedSet SqlFull Temporal Values Dialects ValueKit PostgreSQL MySQL Hash StringFuns Regex RegexFuns.

Close Scope Q_scope.
Close Scope Qc_scope.
Open Scope string_scope.
Open Scope Z_scope.

Import NullValues.

(** OceanBase has two compatibility modes, chosen when a tenant is created and which
    cannot be changed afterwards. *)

(** * MySQL mode

    The semantics of the values is that of MySQL, with the differences which follow, and
    which are established by the source of OceanBase (the grammar
    [src/sql/parser/sql_parser_mysql_mode.y], the default values of the system variables
    [ob_system_variable_init.json], [deps/oblib/src/common/sql_mode/ob_sql_mode.h]) and by
    its test suite ([tools/deploy/mysql_test], expected results):
    - the default collation is [utf8mb4_general_ci], which is case insensitive and [PAD SPACE]:
      ['a' = 'a '] is true and ['a' LIKE 'a '] is false (MySQL 8: [utf8mb4_0900_ai_ci], no padding);
    - the default [sql_mode] is [STRICT_ALL_TABLES, NO_ZERO_IN_DATE, NO_AUTO_CREATE_USER]: there is
      neither [ONLY_FULL_GROUP_BY] (a query may select a column which is not grouped), nor
      [PIPES_AS_CONCAT] ([||] is the logical OR: [length(trim('     hi' || 'dir '))] is 1), nor
      [ERROR_FOR_DIVISION_BY_ZERO];
    - the grammar has [LATERAL] derived tables, [FULL [OUTER] JOIN], [INTERSECT], [EXCEPT] and
      [MINUS] (without [ALL]: [INTERSECT ALL] is a syntax error), [ROLLUP], [CUBE], [GROUPING SETS],
      [WITH RECURSIVE], [ROWS] and [RANGE] window frames (no [GROUPS]), but no [FILTER] clause on
      aggregates, and [NULLS FIRST/LAST] only in the [ORDER BY] of [ARRAY_AGG]. *)

Definition ob_my_supports (f : feature) : bool :=
  match f with
  | F_Frame_Groups | F_Filter_Agg | F_Nulls_Order | F_Intersect_All | F_Except_All
  | F_Fetch_Ties | F_Fetch_Percent => false
  | _ => true
  end.

(** The default session: [utf8mb4_general_ci] (PAD SPACE, case insensitive), [sql_mode] without
    [ONLY_FULL_GROUP_BY] nor [PIPES_AS_CONCAT], [group_concat_max_len] = 1024
    ([src/share/system_variable/ob_system_variable_init.json]). *)
Definition ob_my_default_session : my_session := mk_my_session true Coll_General_CI 4 false false 1024%N 0.

Definition OceanBaseMySQL : vsem := mysql_vs ob_my_default_session "OceanBase (MySQL mode)" ob_my_supports.

(** * Oracle mode

    - the empty string is NULL ([ObObj::is_null_oracle]: NULL, or a character value of length 0): a string function whose result is empty returns NULL, 
      [length('')] is NULL, and ['' = ''] is UNKNOWN;
    - there is no boolean type: a condition is not a value;
    - strings are compared byte by byte; a string compared with a number is converted to
      a number, and the comparison is UNKNOWN when it is not one (Oracle signals an
      error);
    - NULLs are the largest values of [ORDER BY]; [NULLS FIRST/LAST] is available
      (assumed from Oracle, to be verified);
    - [/] is the exact division, a division by zero fails ([ORA-01476: divisor is equal to zero]);
      an arithmetic operation or a comparison on a string which is not a number fails
      ([ORA-01722: invalid number]);
      [MOD(x, 0)] is [x];
    - [||] and [CONCAT] treat a NULL operand as the empty string: [NULL || 'a'] is ['a'];
    - [GREATEST] and [LEAST] are NULL as soon as one argument is NULL ([ObExprLeastGreatest::calc_oracle]);
    - [SUBSTR] with a start of 0 starts at 1 ([ObExprSubstr]), and returns NULL for a length below 1;
    - [LIKE] is case sensitive and has no default escape character;
    - [VARIANCE] is the variance of the sample; [LISTAGG] ignores the NULLs.
    [MINUS] is [EXCEPT]. *)

Definition ora_isnull (v : value) : bool :=
  match v with
  | Value_string (Some EmptyString) => true
  | _ => is_null v
  end.

Definition ora_compare (v1 v2 : value) : option comparison :=
  if (ora_isnull v1 || ora_isnull v2)%bool then None
  else match v1, v2 with
       | Value_string (Some a), Value_string (Some b) => Some (string_compare a b)
       | _, _ => match strict_conv v1, strict_conv v2 with
                 | Some a, Some b => Some (num_cmp a b)
                 | _, _ => None
                 end
       end.

(** [ORA-01722]: a string which is not the text of a number, where a number is expected *)
Definition ora_bad_number (v : value) : bool :=
  match v with
  | Value_string (Some s) => negb (ora_isnull v) && match strict_conv v with Some _ => false | None => true end
  | _ => false
  end.

Definition is_number_value (v : value) : bool :=
  match v with Value_Z (Some _) | Value_Q (Some _) => true | _ => false end.

Definition ora_comparisons : list string := 
  ("=" :: "<>" :: "!=" :: "<" :: "<=" :: ">" :: ">=" :: "between" :: "not between" :: "in" :: "not in" :: nil)%string.

Definition ora_pred_error (p : string) (l : list value) : bool :=
  existsb (String.eqb p) ora_comparisons && existsb is_number_value l && existsb ora_bad_number l.

(** arithmetic: NULL on a NULL operand, [ORA-01722] on a string which is not a number *)
Definition ora_fun2 (f : num -> num -> value) (l : list value) : value :=
  match l with
  | v1 :: v2 :: nil =>
    if (ora_bad_number v1 || ora_bad_number v2)%bool then Value_Err "ORA-01722: invalid number"
    else match strict_conv v1, strict_conv v2 with
         | Some a, Some b => f a b
         | _, _ => Value_Z None
         end
  | _ => Value_Z None
  end.

Definition ora_order (a b : value) : comparison :=
  match ora_compare a b with Some c => c | None => value_compare a b end.

Definition ora_truth (v : value) : bool3 :=
  match v with
  | Value_bool (Some true) => true3
  | Value_bool (Some false) => false3
  | _ => unknown3
  end.

Definition ora_eq3 (a b : value) : bool3 := cmp_pred ora_compare is_Eq (a :: b :: nil).

Definition ora_like (v p : value) : bool3 :=
  if (ora_isnull v || ora_isnull p)%bool then unknown3
  else match text_of v, text_of p with
       | Some s, Some p => bool3_of_bool (like_gen None p s)
       | _, _ => unknown3
       end.

Definition ora_pred_table : list (string * (list value -> bool3)) :=
  comparison_table ora_compare ++
  ("is null", unary3 (fun v => bool3_of_bool (ora_isnull v)))
  :: ("is not null", unary3 (fun v => bool3_of_bool (negb (ora_isnull v))))
  :: ("like", binary3 ora_like)
  :: ("not like", binary3 (fun v p => negb3 (ora_like v p)))
  :: nil.

Definition ora_str1 (f : string -> value) (l : list value) : value :=
  match l with
  | v :: nil => if ora_isnull v then Value_string None 
                else match text_of v with Some s => f s | None => Value_string None end
  | _ => Value_string None
  end.

(** the string functions: [''] is NULL, and a result [''] is NULL *)
Definition ora_skit : skit :=
  mk_skit (fun v => if ora_isnull v then None else text_of v)
          (fun v => match lenient v with Some (Num_Z z) => Some z | Some (Num_Q q) => Some (Qc_trunc q) | None => None end)
          (fun s => match s with EmptyString => Value_string None | _ => Value_string (Some s) end)
          (Value_string None).

(** the regular expressions of Oracle: POSIX syntax with the Perl escapes, case-sensitive by default,
    [.] does not match a line break unless the flag [n], groups [\n] in a replacement *)
Definition ora_rx : rx_env := mk_rx_env ora_skit fl_ora false false false false "ORA-12733: regular expression too long or invalid".

Definition ora_str_fun1 (f : string -> string) := ora_str1 (fun s => Value_string (Some (f s))).

(** [NULL || x] is [x]; the result is NULL when both are. *)
Definition ora_concat (l : list value) : value :=
  if forallb ora_isnull l then Value_string None
  else Value_string (Some (fold_left (fun acc v => if ora_isnull v then acc 
                                                   else match text_of v with Some s => acc ++ s | None => acc end) 
                                     l EmptyString)).

(** The numeric arguments of [SUBSTR] are truncated: [SUBSTR('OceanBase', -3, 2.1)] has 2 characters
    (documentation; [ObExprUtil::get_trunc_int64] in the source). *)
Definition ora_z_arg (v : value) : option Z :=
  match strict_conv v with
  | Some (Num_Z z) => Some z
  | Some (Num_Q q) => Some (Qc_trunc q)
  | None => None
  end.

Definition ora_substr (l : list value) : value :=
  match l with
  | s :: p :: rest =>
    if ora_isnull s then Value_string None
    else match text_of s, ora_z_arg p, rest with
         | Some s, Some p, nil => 
           let p' := if Z.eqb p 0 then 1 else if Z.ltb p 0 then (Z.of_nat (String.length s) + p + 1) else p in
           Value_string (Some (sql_substring s p' None))
         | Some s, Some p, n :: nil =>
           match ora_z_arg n with
           | Some n => 
             if Z.ltb n 1 then Value_string None
             else let p' := if Z.eqb p 0 then 1 else if Z.ltb p 0 then (Z.of_nat (String.length s) + p + 1) else p in
                  Value_string (Some (sql_substring s p' (Some n)))
           | None => Value_string None
           end
         | _, _, _ => Value_string None
         end
  | _ => Value_string None
  end.

Definition ora_mod (a b : num) : option num :=
  if num_is_zero b then Some a else num_rem a b.

(** * Dates in Oracle mode

    A [DATE] has a date and a time, to the second ([Value_T] of kind 2 without fractional digits); a
    [TIMESTAMP] has fractional seconds. [date + n] and [date - n] add [n] days, a number which may have a
    fraction; [date - date] is the number of days between them, with a fraction. Converted to a text, a date
    follows [NLS_DATE_FORMAT], ['DD-MON-RR'] by default ([ob_system_variable_init.json]). [TO_DATE] reads the
    patterns [YYYY YY MM MON DD HH24 HH MI SS] and copies the other characters. *)
Definition ora_date_text (t : Z) : string := pg_format 20 t "DD-MON-YY".

Fixpoint ora_parse_date (fuel : nat) (fmt s : string) (acc : Z * Z * Z * Z * Z * Z) : option (Z * Z * Z * Z * Z * Z) :=
  match fuel with
  | O => None
  | S f =>
    let '(y, mo, d, h, mi, se) := acc in
    let num (k : nat) (p : string) (set : Z -> Z * Z * Z * Z * Z * Z) :=
        let len := String.length p in
        (* a field of at most [k] digits *)
        let digits := (fix take (n : nat) (x : string) : string :=
                         match n, x with
                         | S n', String c r => if (Nat.leb 48 (nat_of_ascii c) && Nat.leb (nat_of_ascii c) 57)%bool then String c (take n' r) else EmptyString
                         | _, _ => EmptyString end) k s in
        match Temporal.digits_of digits with
        | Some v => ora_parse_date f (substring len (String.length fmt - len) fmt) (substring (String.length digits) (String.length s - String.length digits) s) (set v)
        | None => None
        end in
    if String.prefix "YYYY" fmt then num 4%nat "YYYY" (fun v => (v, mo, d, h, mi, se))
    else if String.prefix "HH24" fmt then num 2%nat "HH24" (fun v => (y, mo, d, v, mi, se))
    else if String.prefix "MON" fmt then
      let m3 := Temporal.upper_string (substring 0 3 s) in
      match find (fun i => String.eqb (Temporal.upper_string (substring 0 3 (month_name (Z.of_nat i)))) m3) (seq 1 12) with
      | Some i => ora_parse_date f (substring 3 (String.length fmt - 3) fmt) (substring 3 (String.length s - 3) s) (y, Z.of_nat i, d, h, mi, se)
      | None => None end
    else if String.prefix "YY" fmt then num 2%nat "YY" (fun v => (2000 + v, mo, d, h, mi, se))
    else if String.prefix "MM" fmt then num 2%nat "MM" (fun v => (y, v, d, h, mi, se))
    else if String.prefix "DD" fmt then num 2%nat "DD" (fun v => (y, mo, v, h, mi, se))
    else if String.prefix "HH" fmt then num 2%nat "HH" (fun v => (y, mo, d, v, mi, se))
    else if String.prefix "MI" fmt then num 2%nat "MI" (fun v => (y, mo, d, h, v, se))
    else if String.prefix "SS" fmt then num 2%nat "SS" (fun v => (y, mo, d, h, mi, v))
    else match fmt, s with
         | EmptyString, EmptyString => Some acc
         | String _ fr, String _ sr => ora_parse_date f fr sr acc
         | _, _ => None
         end
  end.

Definition ora_to_date (s fmt : string) : value :=
  match ora_parse_date (S (String.length fmt + String.length s)) (Temporal.upper_string fmt) s (1, 1, 1, 0, 0, 0) with
  | Some (y, mo, d, h, mi, se) =>
    if valid_date y mo d && (h <? 24) && (mi <? 60) && (se <? 60)
    then VTs (ts_of (days_from_civil y mo d) (((h * 60 + mi) * 60 + se) * 1000000)) 0
    else Value_Err "ORA-01847: day of month must be between 1 and last day of month"
  | None => Value_Err "ORA-01861: literal does not match format string"
  end%Z.

(** [ADD_MONTHS(d, n)]: the last day of a month gives the last day of the result month *)
Definition ora_add_months (t n : Z) : Z :=
  let days := ts_days t in
  let '(y, m, d) := civil_from_days days in
  let r := add_months days n in
  let r := if Z.eqb d (days_in_month y m) 
           then let '(y', m', _) := civil_from_days r in days_from_civil y' m' (days_in_month y' m') else r in
  ts_of r (ts_usec t).

(** [MONTHS_BETWEEN(a, b)]: whole months when the days are equal or both the last of their month,
    otherwise the difference of the days counts as a fraction of 31 *)
Definition ora_months_between (a b : Z) : Qc :=
  let '(ya, ma, da) := civil_from_days (ts_days a) in
  let '(yb, mb, db) := civil_from_days (ts_days b) in
  let m := (ya * 12 + ma) - (yb * 12 + mb) in
  if Z.eqb da db || (Z.eqb da (days_in_month ya ma) && Z.eqb db (days_in_month yb mb))
  then Qc_of_Z m
  else Qcplus (Qc_of_Z m) (Qcdiv (Qcplus (Qc_of_Z (da - db)) (Qcdiv (Qc_of_Z (ts_usec a - ts_usec b)) (Qc_of_Z usec_per_day))) (Qc_of_Z 31)).

Definition ora_date_arith (minus : bool) (old : list value -> value) (l : list value) : value :=
  match l with
  | v1 :: v2 :: nil =>
    match to_ts v1, to_ts v2 with
    | Some a, Some b => if minus then value_of_num (Num_Q (Qcdiv (Qc_of_Z (a - b)) (Qc_of_Z usec_per_day))) else Value_Err "ORA-00975: date + date not allowed"
    | Some a, None => match strict_conv v2 with
                      | Some n => VTs (a + (if minus then - 1 else 1) * Qc_round (Qcmult (Qc_of_num n) (Qc_of_Z usec_per_day))) 0
                      | None => if is_null v2 then Value_T None else Value_Err "ORA-00932: inconsistent datatypes" end
    | None, Some b => match strict_conv v1, minus with
                      | Some n, false => VTs (b + Qc_round (Qcmult (Qc_of_num n) (Qc_of_Z usec_per_day))) 0
                      | _, _ => if is_null v1 then Value_T None else Value_Err "ORA-00932: inconsistent datatypes" end
    | None, None => old l
    end
  | _ => old l
  end.

Definition ora_symbol_table : list (string * (list value -> value)) :=
  let conv := strict_conv in
  let plus := ora_date_arith false (ora_fun2 (fun a b => value_of_num (num_plus a b))) in
  let minus := ora_date_arith true (ora_fun2 (fun a b => value_of_num (num_minus a b))) in
  let mult := ora_fun2 (fun a b => value_of_num (num_mult a b)) in
  let opp := num_fun1 conv num_opp in
  let div := ora_fun2 (fun a b => match num_div_exact a b with 
                                  | Some n => value_of_num n 
                                  | None => Value_Err "ORA-01476: divisor is equal to zero" end) in
     ("plus", plus) :: ("+", plus)
  :: ("minus", minus) :: ("-", minus)
  :: ("mult", mult) :: ("*", mult)
  :: ("opp", opp) :: ("neg", opp)
  :: ("/", div)
  :: ("mod", ora_fun2 (fun a b => match ora_mod a b with Some n => value_of_num n | None => Value_Z None end))
  :: ("abs", num_fun1 conv num_abs)
  :: ("sign", num_fun1 conv num_sign)
  :: ("floor", num_fun1 conv num_floor)
  :: ("ceil", num_fun1 conv num_ceil)
  :: ("round", fun l => match l with
                        | v :: nil => num_fun1 conv (fun a => num_round a 0) l
                        | v :: d :: nil => match conv v, z_arg d with
                                           | Some a, Some d => value_of_num (num_round a d) 
                                           | _, _ => Value_Z None end
                        | _ => Value_Z None end)
  :: ("trunc", fun l => match l with
                        | v :: nil => num_fun1 conv (fun a => num_trunc a 0) l
                        | v :: d :: nil => match conv v, z_arg d with
                                           | Some a, Some d => value_of_num (num_trunc a d) 
                                           | _, _ => Value_Z None end
                        | _ => Value_Z None end)
  :: ("power", num_fun2 conv num_power)
  :: ("regexp_count", rx_count ora_rx) :: ("regexp_instr", rx_instr ora_rx)
  :: ("regexp_substr", rx_substr ora_rx) :: ("regexp_replace", rx_replace ora_rx)
  (* [DECODE (e, s1, r1, ..., [default])]: the first [ri] whose [si] equals [e], two NULLs being equal *)
  :: ("decode", fun l => match l with
                         | e :: rest =>
                           let fix go (r : list value) :=
                               match r with
                               | s1 :: r1 :: r' => if (ora_isnull e && ora_isnull s1) ||
                                                      (negb (ora_isnull e) && negb (ora_isnull s1) &&
                                                       match ora_compare e s1 with Some Eq => true | _ => false end)
                                                   then r1 else go r'
                               | d :: nil => d
                               | nil => Value_string None
                               end in
                           go rest
                         | nil => Value_Err "ORA-00938: not enough arguments for function" end)
  :: ("greatest", extremum_strict ora_isnull ora_order is_Gt)
  :: ("least", extremum_strict ora_isnull ora_order is_Lt)
  (* conditional expressions *)
  :: ("coalesce", fun l => match filter (fun v => negb (ora_isnull v)) l with 
                           | v :: _ => v 
                           | nil => Value_Z None end)
  :: ("nvl", fun l => match l with 
                      | a :: b :: nil => if ora_isnull a then b else a 
                      | _ => Value_Z None end)
  :: ("nvl2", fun l => match l with 
                       | a :: b :: c :: nil => if ora_isnull a then c else b
                       | _ => Value_Z None end)
  :: ("nullif", fun l => match l with
                         | v1 :: v2 :: nil => match ora_eq3 v1 v2 with
                                              | true3 => default_value (type_of_value v1)
                                              | _ => v1 end
                         | _ => Value_Z None end)
  :: ("case", case_by ora_truth)
  (* strings *)
  :: ("||", fun l => ora_concat (map (fun v => match to_ts v with Some t => Value_string (Some (ora_date_text t)) | None => v end) l))
  :: ("concat", fun l => ora_concat (map (fun v => match to_ts v with Some t => Value_string (Some (ora_date_text t)) | None => v end) l))
  (* dates *)
  :: ("to_date", fun l => match l with
                          | v :: f :: nil => match text_of v, text_of f with Some s, Some fmt => ora_to_date s fmt | _, _ => Value_T None end
                          | v :: nil => match text_of v with Some s => ora_to_date s "DD-MON-RR" | None => Value_T None end
                          | _ => Value_T None end)
  :: ("cast_date", fun l => match l with 
                            | Value_string (Some s) :: nil => match parse_timestamp s with Some t => VTs t 0 | None => Value_Err "ORA-01861: literal does not match format string" end
                            | v :: nil => match to_ts v with Some t => VTs t 0 | None => Value_T None end
                            | _ => Value_T None end)
  :: ("to_char", fun l => match l with
                          | v :: f :: nil => match to_ts v, text_of f with 
                                             | Some t, Some fmt => Value_string (Some (pg_format (S (String.length fmt)) t fmt))
                                             | None, _ => Value_string (text_of v)
                                             | _, _ => Value_string None end
                          | v :: nil => match to_ts v with Some t => Value_string (Some (ora_date_text t)) | None => Value_string (text_of v) end
                          | _ => Value_string None end)
  :: ("sysdate", fun _ => VTs statement_time 0)
  :: ("systimestamp", fun _ => VTsTz statement_time 6)
  :: ("add_months", fun l => match l with
                             | v :: n :: nil => match to_ts v, strict_conv n with
                                                | Some t, Some k => VTs (ora_add_months t (Qc_trunc (Qc_of_num k))) 0
                                                | _, _ => Value_T None end
                             | _ => Value_T None end)
  :: ("last_day", fun l => match l with
                           | v :: nil => match to_ts v with
                                         | Some t => let '(y, m, _) := civil_from_days (ts_days t) in VTs (ts_of (days_from_civil y m (days_in_month y m)) (ts_usec t)) 0
                                         | None => Value_T None end
                           | _ => Value_T None end)
  :: ("months_between", fun l => match l with
                                 | a :: b :: nil => match to_ts a, to_ts b with
                                                    | Some x, Some y => Value_Q (Some (ora_months_between x y))
                                                    | _, _ => Value_Q None end
                                 | _ => Value_Q None end)
  :: ("extract", fun l => match l with
                          | Value_string (Some fld) :: v :: nil => 
                            match to_ts v with
                            | Some t => let '(y, m, d) := civil_from_days (ts_days t) in
                                        match string_map upper_ascii fld with
                                        | "YEAR" => Value_Z (Some y) | "MONTH" => Value_Z (Some m) | "DAY" => Value_Z (Some d)
                                        | "HOUR" => Value_Z (Some (ts_usec t / 3600000000)) 
                                        | "MINUTE" => Value_Z (Some ((ts_usec t / 60000000) mod 60))
                                        | "SECOND" => Value_Z (Some ((ts_usec t / 1000000) mod 60))
                                        | _ => Value_Err "ORA-30076: invalid extract field for extract source" end
                            | None => Value_Z None end
                          | _ => Value_Z None end)
  :: ("length", ora_str1 (fun s => Value_Z (Some (Z.of_nat (String.length s)))))
  :: ("upper", ora_str_fun1 upper_s) :: ("lower", ora_str_fun1 lower_s)
  :: ("trim", ora_str_fun1 (fun s => string_rtrim (string_ltrim s)))
  (* [LTRIM (s, set)], [RTRIM (s, set)]: a set of characters; [TRIM (c FROM s)] *)
  :: ("ltrim", f_trim_set ora_skit 1) :: ("rtrim", f_trim_set ora_skit 2)
  :: ("trim_both", f_trim_set ora_skit 0) :: ("trim_leading", f_trim_set ora_skit 1) :: ("trim_trailing", f_trim_set ora_skit 2)
  (* [LPAD], [RPAD] (a space by default), [TRANSLATE], [INITCAP], [ASCII], [CHR]; [''] is NULL *)
  :: ("lpad", f_pad ora_skit true false) :: ("rpad", f_pad ora_skit false false)
  :: ("translate", f_translate ora_skit)
  :: ("initcap", f_text1 ora_skit initcap_cp)
  :: ("ascii", fun l => match texts ora_skit l with
                        | Some (s :: nil) => Value_Z (Some (ord_of s))
                        | _ => Value_Z None end)
  :: ("chr", fun l => match l with
                      | v :: nil => match sk_int ora_skit v with
                                    | Some n => Value_string (Some (string_of_bytes (my_char_bytes n)))
                                    | None => Value_string None end
                      | _ => Value_Err "ORA-00909: invalid number of arguments" end)
  :: ("substr", ora_substr)
  :: ("replace", fun l => match l with
                          | s :: f :: nil => match text_of s, text_of f with
                                             | Some s, Some f => Value_string (Some (string_replace s f EmptyString))
                                             | _, _ => Value_string None end
                          | s :: f :: t :: nil => match text_of s, text_of f, (if ora_isnull t then Some EmptyString else text_of t) with
                                                  | Some s, Some f, Some t => Value_string (Some (string_replace s f t))
                                                  | _, _, _ => Value_string None end
                          | _ => Value_string None end)
  :: ("instr", fun l => match l with
                        | s :: sub :: nil => match text_of s, text_of sub with
                                             | Some s, Some sub => Value_Z (Some (string_index sub s))
                                             | _, _ => Value_Z None end
                        | _ => Value_Z None end)
  (* conversions *)
  :: ("cast_string", fun l => match l with v :: nil => Value_string (text_of v) | _ => Value_string None end)
  :: ("cast_numeric", fun l => match l with
                               | v :: nil => match conv v with Some n => value_of_num n | None => Value_Z None end
                               | _ => Value_Z None end)
  :: ("cast_int", fun l => match l with
                           | v :: nil => match conv v with 
                                         | Some n => value_of_num (num_round n 0)
                                         | None => Value_Z None end
                           | _ => Value_Z None end)
  :: nil.

Definition ora_aggregate_table : list (string * (list value -> value)) :=
     ("count", agg_count_by ora_isnull)
  :: ("count(*)", fun l => Value_Z (Some (Z.of_nat (List.length l))))
  :: ("sum", agg_sum_by ora_isnull strict_conv)
  :: ("avg", agg_avg_by ora_isnull strict_conv)
  :: ("min", agg_extremum_by ora_isnull ora_order is_Lt)
  :: ("max", agg_extremum_by ora_isnull ora_order is_Gt)
  :: ("listagg", agg_concat_by ora_isnull "")
  :: ("listagg_sep", agg_concat_sep_by ora_isnull "")
  :: ("variance", agg_var_by ora_isnull strict_conv true)
  :: ("var_samp", agg_var_by ora_isnull strict_conv true)
  :: ("var_pop", agg_var_by ora_isnull strict_conv false)
  :: nil.

(** The constructs of OceanBase in Oracle mode, from its documentation (the repository
    [oceanbase-doc], pages of the SQL reference of the Oracle mode): [UNION [ALL]], [INTERSECT]
    and [MINUS] (no [ALL] for the last two, and no [EXCEPT]); [FULL], [LEFT] and [RIGHT]
    [OUTER JOIN]; [LATERAL] derived tables (since V4.3.1); [ROWS] and [RANGE] window frames
    (no [GROUPS]); [ORDER BY ... NULLS FIRST/LAST]; [OFFSET ... FETCH FIRST ... ROWS]. There is no
    [FILTER] clause on aggregates, and no boolean type. The source of OceanBase does not contain
    the parser of the Oracle mode: what is established by the source (the engine is shared)
    is stated with the corresponding functions above. *)
Definition ora_supports (f : feature) : bool :=
  match f with
  | F_Intersect_All | F_Except_All | F_Frame_Groups | F_Filter_Agg | F_Cond_Value => false
  (* ORA-00979: not a GROUP BY expression *)
  | F_Bare_Column => false
  | _ => true
  end.

Definition canon_ora (v : value) : value :=
  if ora_isnull v then Value_Z None else canon_numeric v.

Definition OceanBaseOracle : vsem :=
  mk_vsem "OceanBase (Oracle mode)"
          (table_of_list (like_table ora_skit false (fun c => c) (fun c => c) None
                          ++ ("regexp_like", rx_like ora_rx false) :: ("not regexp_like", fun l => negb3 (rx_like ora_rx false l))
                          :: ora_pred_table))
          (table_of_list ora_symbol_table)
          (table_of_list ora_aggregate_table)
          ora_isnull
          ora_truth
          (fun b => match b with true3 => Value_Z (Some 1) | false3 => Value_Z (Some 0) | unknown3 => Value_Z None end)
          ora_eq3
          ora_order
          canon_ora
          false
          ora_supports
          false
          (fun p l => ora_pred_error p l || bad_escape ora_skit p l || rx_bad ora_rx ("regexp_like" :: "not regexp_like" :: nil)%string p l)
          (* a [NUMBER] has no display scale: [1.50] is [1.5] *)
          (fun v => match v with Value_D (Some (q, _, _)) => Value_Q (Some q) | _ => v end)
          (fun _ => false)
          (fun _ _ l => l).
