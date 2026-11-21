(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**                            The MySQL dialect                                    *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String Ascii ZArith NArith QArith Qcanon.

Require Import Bool3 OrderedSet SqlFull Temporal Json Values Dialects ValueKit Collation Hash StringFuns Regex RegexFuns Aggregates TemporalFuns JsonFuns SystemFuns.

Close Scope Q_scope.
Close Scope Qc_scope.
Open Scope string_scope.
Open Scope Z_scope.

Import NullValues.

(** * MySQL 8.0, with the default [sql_mode] and the default collation [utf8mb4_0900_ai_ci]

    - there is no boolean type: conditions are the integers 1, 0 and NULL, and a value
      which is used as a condition is true when it is a non-zero number (strings are read
      as numbers);
    - a comparison of two strings is case insensitive; a comparison with a number is a
      comparison of numbers, the string being read as a number;
    - NULLs are the smallest values of [ORDER BY]; [NULLS FIRST/LAST] does not exist;
    - [/] is the exact division, [DIV] the integer division, [%] and [MOD] have the sign
      of the dividend; a division by zero is NULL;
    - [||] is the logical OR, [&&] the logical AND; [CONCAT] is NULL as soon as one
      argument is NULL, [CONCAT_WS] skips the NULLs;
    - [GREATEST] and [LEAST] are NULL as soon as one argument is NULL;
    - the strings of [SUBSTRING] are counted from the end for a negative start;
    - [LIKE] is case insensitive, with [\] as the escape character;
    - [VARIANCE] is the variance of the population.
    Accents are not folded; sizes of integers and floating-point rounding are not
    modelled. *)

(** The collation of strings. Both collations of MySQL and of OceanBase which are the
    default ones are case insensitive; they differ by the treatment of the trailing spaces:
    - [utf8mb4_0900_ai_ci], the default of MySQL 8, is [NO PAD]: ['a'] and ['a '] are different;
    - [utf8mb4_general_ci], the default of OceanBase (collation 45, from the default of the
      system variable [collation_server]), is [PAD SPACE]: ['a' = 'a '], but ['a' LIKE 'a '] is false.
    Accents are not folded. *)
(** * The session

    The system variables which change the result of a query, with the values which the server
    uses by default. The variables which only change the parsing of the text of a query
    ([ANSI_QUOTES], [NO_BACKSLASH_ESCAPES], [HIGH_NOT_PRECEDENCE]) do not appear: the syntax of
    [SqlFull] is abstract. [ERROR_FOR_DIVISION_BY_ZERO] and the strict modes only concern [INSERT]
    and [UPDATE] (in a [SELECT], a division by zero is NULL with a warning). *)
Record my_session : Type :=
  mk_my_session
    {
      (** the default collation: [PAD SPACE]? *)
      ms_pad : bool;
      (** the default collation *)
      ms_coll : collation;
      (** [div_precision_increment] *)
      ms_div_incr : nat;
      (** [sql_mode] contains [PIPES_AS_CONCAT]: [||] is the concatenation, not the logical OR *)
      ms_pipes_as_concat : bool;
      (** [sql_mode] contains [ONLY_FULL_GROUP_BY] *)
      ms_only_full_group_by : bool;
      (** [group_concat_max_len]: the result of [GROUP_CONCAT] is truncated to this length *)
      ms_group_concat_max_len : N;
      (** the library of the regular expressions: 0 ICU (MySQL 8), 1 PCRE (MariaDB), 2 RE2 (TiDB) *)
      ms_regex : nat
    }.

Section Session.

Variable ss : my_session.

Let pad := ms_pad ss.

Let coll := ms_coll ss.

(** The key of a string for a comparison: its weights under the collation ([Collation.v]) *)
Definition coll_key (s : string) : string := Collation.coll_key coll pad s.

(** the system variable [div_precision_increment], whose default value is 4 in MySQL and in OceanBase *)
Let div_precision_increment : nat := ms_div_incr ss.

Definition my_isnull := is_null.

(** the collation of a comparison: the explicit collation of an operand ([COLLATE]), otherwise the
    collation of the session; two different explicit collations are an error (see [my_pred_error]) *)
Definition explicit_coll (v : value) : option (collation * bool) :=
  match v with Value_C (Some (_, n)) => my_collation_of_name n | _ => None end.

Definition str_value (v : value) : option string :=
  match v with Value_string (Some s) => Some s | Value_C (Some (s, _)) => Some s | _ => None end.

Definition my_compare_base (v1 v2 : value) : option comparison :=
  if (is_null v1 || is_null v2)%bool then None
  else 
  (* a date or a time with a string: the string is read as a value of the same type; with a number: the
     temporal value is a number ([Arg_comparator::set_cmp_func]) *)
  match v1, v2 with
  | Value_T (Some _), Value_T (Some _) => temporal_compare v1 v2
  | Value_T (Some _), Value_string (Some t) => match parse_like v1 t with Some w => temporal_compare v1 w | None => None end
  | Value_string (Some t), Value_T (Some _) => match parse_like v2 t with Some w => temporal_compare w v2 | None => None end
  | Value_T (Some _), _ | _, Value_T (Some _) =>
    (* an integer with a date or a datetime: the integer read as a datetime *)
    let as_dt (t n : value) := 
        match to_ts t, n with
        | Some x, Value_Z (Some z) => match my_number_to_datetime z with Some y => Some (x, y) | None => None end
        | _, _ => None end in
    match as_dt v1 v2, as_dt v2 v1 with
    | Some (x, y), _ => Some (Z.compare x y)
    | None, Some (x, y) => Some (Z.compare y x)
    | None, None =>
    let num v := match my_temporal_number v with Some (q, _) => Some (Num_Q q) | None => lenient v end in
    match num v1, num v2 with Some a, Some b => Some (num_cmp a b) | _, _ => None end
    end
  | _, _ =>
  match str_value v1, str_value v2 with
       | Some a, Some b => 
         let (c, p) := match explicit_coll v1, explicit_coll v2 with
                       | Some cp, _ | None, Some cp => cp
                       | None, None => (coll, pad)
                       end in
         Some (string_compare (Collation.coll_key c p a) (Collation.coll_key c p b))
       | _, _ => match lenient v1, lenient v2 with
                 | Some a, Some b => Some (num_cmp a b)
                 | _, _ => None
                 end
       end
  end.

(** two JSON values are compared by their normalized texts; a JSON scalar with a SQL value as a SQL
    value ([Item_func_json...], [compare_json]) *)
Definition my_compare (v1 v2 : value) : option comparison :=
  match v1, v2 with
  | Value_J (Some (a, _)), Value_J (Some (b, _)) => Some (string_compare a b)
  | _, _ => my_compare_base (json_scalar v1) (json_scalar v2)
  end.

Definition my_order (a b : value) : comparison :=
  match my_compare a b with Some c => c | None => value_compare a b end.


Definition my_eq3 (a b : value) : bool3 := cmp_pred my_compare is_Eq (a :: b :: nil).

(** [x <=> y]: equality which is never UNKNOWN. *)
Definition my_null_safe_eq (a b : value) : bool3 :=
  match is_null a, is_null b with
  | true, true => true3
  | false, false => my_eq3 a b
  | _, _ => false3
  end.


Definition my_pred_table : list (string * (list value -> bool3)) :=
  comparison_table my_compare ++
  ("<=>", binary3 my_null_safe_eq)
  :: ("is null", unary3 (fun v => bool3_of_bool (is_null v)))
  :: ("is not null", unary3 (fun v => bool3_of_bool (negb (is_null v))))
  :: ("is true", unary3 (truth_is true3))
  :: ("is not true", unary3 (fun v => negb3 (truth_is true3 v)))
  :: ("is false", unary3 (truth_is false3))
  :: ("is not false", unary3 (fun v => negb3 (truth_is false3 v)))
  :: ("is unknown", unary3 (truth_is unknown3))
  :: ("is not unknown", unary3 (fun v => negb3 (truth_is unknown3 v)))
  :: ("like", binary3 (fun v p => match text_of v, text_of p with
                                  | Some s, Some p => bool3_of_bool (coll_like coll (Some 92) p s)
                                  | _, _ => unknown3 end))
  :: ("not like", binary3 (fun v p => negb3 (match text_of v, text_of p with
                                  | Some s, Some p => bool3_of_bool (coll_like coll (Some 92) p s)
                                  | _, _ => unknown3 end)))
  :: ("true", fun _ => true3)
  :: ("false", fun _ => false3)
  :: ("unknown", fun _ => unknown3)
  :: nil.



(** the scale of [ROUND (x, d)] and [TRUNCATE (x, d)]: at most [DECIMAL_MAX_SCALE] decimals, 30 in MySQL
    and 38 in MariaDB (the session with PCRE, [ms_regex = 1]); below -400 every value rounds to 0 (doubles are
    below 1e309): the bounds keep [10 ^ d] small *)
Definition clamp_scale (d : Z) : Z := Z.max (-400) (Z.min (if Nat.eqb (ms_regex ss) 1 then 38 else 30) d).






Definition xor3 (a b : bool3) : bool3 :=
  match a, b with
  | unknown3, _ | _, unknown3 => unknown3
  | true3, true3 | false3, false3 => false3
  | _, _ => true3
  end.

Definition my_concat (l : list value) : value :=
  if existsb is_null l then Value_string None
  else Value_string (Some (fold_left (fun acc v => match text_of v with Some s => acc ++ s | None => acc end) 
                                     l EmptyString)).

Definition my_skit : skit := mk_skit text_of z_arg (fun s => Value_string (Some s)) (Value_string None).

(** the regular expressions of the session: ICU (MySQL: groups [$n] in a replacement), PCRE (MariaDB: [\n])
    or RE2 (TiDB: no back reference); case-insensitive under a case-insensitive collation; [.] does not
    match a line break unless the flag [n] *)
Definition my_rx : rx_env :=
  mk_rx_env my_skit
            (match ms_regex ss with 1%nat => fl_pcre | 2%nat => fl_re2 | _ => fl_icu end)
            false
            (match coll with Coll_Binary => false | _ => true end)
            false
            (negb (Nat.eqb (ms_regex ss) 1))
            "Illegal argument to a regular expression".

(** a path with a wildcard *)
Definition json_wild (t : string) : bool := match index 0 "*" t with Some _ => true | None => false end.

(** the JSON functions of TODO 2.8: a document, then paths (and values); NULL if one is NULL *)
Definition my_json_update (create replace : bool) (l : list value) : value :=
  match l with
  | d :: rest =>
    if existsb is_null l then Value_J None
    else match my_json_doc d with
         | Some (Some j) =>
           let fix go (r : list value) (acc : json) : option json :=
               match r with
               | nil => Some acc
               | p :: v :: r' => match text_of p with
                                 (* a path with [*] or [**] is not allowed in the functions which change a document *)
                                 | Some t => if json_wild t then None else
                                             match parse_path t with
                                             | Some st => go r' (set_path create replace st acc (my_json_of_value v))
                                             | None => None end
                                 | None => None end
               | _ => None
               end in
           match go rest j with Some r => VJ 0 r | None => Value_Err "Invalid JSON path expression" end
         | Some None => Value_J None
         | None => Value_Err "Invalid JSON text in argument 1"
         end
  | nil => Value_Err "Incorrect parameter count"
  end.

Definition my_json_paths (f : list step -> json -> option json) (l : list value) : value :=
  match l with
  | d :: paths =>
    if existsb is_null l then Value_J None
    else match my_json_doc d with
         | Some (Some j) =>
           let r := fold_left (fun acc p => match acc, text_of p with
                                            | Some a, Some t => if json_wild t then None else
                                                                match parse_path t with Some st => f st a | None => None end
                                            | _, _ => None end) paths (Some j) in
           match r with Some r => VJ 0 r | None => Value_Err "Invalid JSON path expression" end
         | Some None => Value_J None
         | None => Value_Err "Invalid JSON text in argument 1"
         end
  | nil => Value_Err "Incorrect parameter count"
  end.

Definition my_json_pathvals (f : list step -> json -> json -> option json) (l : list value) : value :=
  match l with
  | d :: rest =>
    if existsb is_null l then Value_J None
    else match my_json_doc d with
         | Some (Some j) =>
           let fix go (r : list value) (acc : json) : option json :=
               match r with
               | nil => Some acc
               | p :: v :: r' => match text_of p with
                                 | Some t => match parse_path t with
                                             | Some st => match f st acc (my_json_of_value v) with Some a => go r' a | None => None end
                                             | None => None end
                                 | None => None end
               | _ => None
               end in
           match go rest j with Some r => VJ 0 r | None => Value_Err "Invalid JSON path expression" end
         | Some None => Value_J None
         | None => Value_Err "Invalid JSON text in argument 1"
         end
  | nil => Value_Err "Incorrect parameter count"
  end.

Definition my_json_docs (f : json -> json -> json) (l : list value) : value :=
  if existsb is_null l then Value_J None
  else match map my_json_doc l with
       | Some (Some j) :: rest =>
         match fold_left (fun acc d => match acc, d with Some a, Some (Some b) => Some (f a b) | _, _ => None end) rest (Some j) with
         | Some r => VJ 0 r
         | None => Value_Err "Invalid JSON text"
         end
       | _ => Value_Err "Invalid JSON text"
       end.

Definition my_concat_ws (l : list value) : value :=
  match l with
  | sep :: rest => 
    match text_of sep with
    | Some sp => 
      match flat_map (fun v => match text_of v with Some s => s :: nil | None => nil end) rest with
      | nil => Value_string (Some EmptyString)
      | s :: ss => Value_string (Some (fold_left (fun acc x => acc ++ sp ++ x) ss s))
      end
    | None => Value_string None
    end
  | nil => Value_string None
  end.

Definition my_substring (l : list value) : value :=
  match l with
  | s :: p :: nil => 
    match text_of s, z_arg p with
    | Some s, Some p => Value_string (Some (substr_from_end s p None))
    | _, _ => Value_string None
    end
  | s :: p :: n :: nil => 
    match text_of s, z_arg p, z_arg n with
    | Some s, Some p, Some n => Value_string (Some (substr_from_end s p (Some n)))
    | _, _, _ => Value_string None
    end
  | _ => Value_string None
  end.

(** [LOCATE(sub, s [, pos])]: the position of [sub] in [s], starting the search at [pos]; 0 when there is
    none, when [pos] is not a position of [s] (it can be the position after its last character), or when
    [pos] is NULL (the source of MySQL reads a NULL position as 0). *)
Definition my_locate (l : list value) : value :=
  match l with
  | sub :: s :: nil => 
    match text_of sub, text_of s with
    | Some sub, Some s => Value_Z (Some (coll_index coll sub s))
    | _, _ => Value_Z None
    end
  | sub :: s :: pos :: nil => 
    match text_of sub, text_of s with
    | Some sub, Some s => 
      let p := match z_arg pos with Some p => p | None => 0 end in
      let cs := utf8_decode s in
      let n := Z.of_nat (List.length cs) in
      if Z.ltb p 1 || Z.ltb (n + 1) p 
      then Value_Z (Some 0)
      else let rest := Collation.utf8_encode (skipn (Z.to_nat (p - 1)) cs) in
           match coll_index coll sub rest with
           | 0 => Value_Z (Some 0)
           | i => Value_Z (Some (i + p - 1))
           end
    | _, _ => Value_Z None
    end
  | _ => Value_Z None
  end.

(** The composite units of [INTERVAL expr unit] ([DAY_HOUR], [HOUR_SECOND], ...): [expr] is read as a list of
    numbers separated by any non-digit, aligned on the right with the parts of the unit ([INTERVAL 1 DAY_HOUR]
    is one hour, [INTERVAL '1 2' DAY_HOUR] one day and two hours); a leading [-] negates the interval
    ([get_interval_value], [sql/item_timefunc.cc]). The units with microseconds are not modelled. *)
Definition my_unit_parts (u : string) : option (list (Z * Z * Z)) :=
  (* each part as (months, days, microseconds) per unit *)
  let Y := (12, 0, 0) in let Mo := (1, 0, 0) in let D := (0, 1, 0) in
  let H := (0, 0, 3600000000) in let Mi := (0, 0, 60000000) in let S := (0, 0, 1000000) in
  match u with
  | "YEAR_MONTH" => Some (Y :: Mo :: nil) | "DAY_HOUR" => Some (D :: H :: nil)
  | "DAY_MINUTE" => Some (D :: H :: Mi :: nil) | "DAY_SECOND" => Some (D :: H :: Mi :: S :: nil)
  | "HOUR_MINUTE" => Some (H :: Mi :: nil) | "HOUR_SECOND" => Some (H :: Mi :: S :: nil)
  | "MINUTE_SECOND" => Some (Mi :: S :: nil)
  | _ => None
  end%string%Z.

Fixpoint my_digit_groups (s : string) (cur : option Z) (acc : list Z) : list Z :=
  match s with
  | EmptyString => rev (match cur with Some z => z :: acc | None => acc end)
  | String c r => let n := Z.of_nat (Ascii.nat_of_ascii c) in
                  if (48 <=? n)%Z && (n <=? 57)%Z
                  then my_digit_groups r (Some ((match cur with Some z => z | None => 0 end) * 10 + (n - 48))%Z) acc
                  else my_digit_groups r None (match cur with Some z => z :: acc | None => acc end)
  end.

Definition my_composite_interval (ps : list (Z * Z * Z)) (t : string) : option (Z * Z * Z) :=
  let neg := match t with String "-"%char _ => true | _ => false end in
  let gs := my_digit_groups t None nil in
  if Nat.ltb (List.length ps) (List.length gs) || Nat.eqb (List.length gs) 0 then None
  else let ps' := skipn (List.length ps - List.length gs) ps in
       let '(a, b, c) := fold_left (fun (acc : Z * Z * Z) pg => let '(a, b, c) := acc in let '((pa, pb, pc), g) := pg in
                                      ((a + pa * g)%Z, (b + pb * g)%Z, (c + pc * g)%Z)) (combine ps' gs) (0, 0, 0)%Z in
       Some (if neg then (- a, - b, - c)%Z else (a, b, c)).

Definition my_symbol_table_raw : list (string * (list value -> value)) :=
  let conv := lenient in
  let with_interval (sign : Z) (f : list value -> value) (l : list value) :=
      match l with
      | d :: Value_V iv :: nil => my_date_add sign d (Value_V iv)
      | Value_V iv :: d :: nil => if Z.eqb sign 1 then my_date_add 1 d (Value_V iv) else f l
      | _ => f l end in
  let plus := with_interval 1 (my_arith2 (Some Z.add) my_dplus (num_fun2 conv (fun a b => Some (num_plus a b)))) in
  let minus := with_interval (-1) (my_arith2 (Some Z.sub) my_dminus (num_fun2 conv (fun a b => Some (num_minus a b)))) in
  let mult := my_arith2 (Some Z.mul) my_dmult (num_fun2 conv (fun a b => Some (num_mult a b))) in
  let opp l := match l with
               | Value_D (Some (q, f, s)) :: nil => VDec (Qcopp q) f s
               | _ => num_fun1 conv num_opp l
               end in
  let div := my_arith2 None (my_ddiv div_precision_increment) (num_fun2 conv num_div_exact) in
  let idiv := num_fun2 conv num_div_trunc in
  let modulo := num_fun2 conv num_rem in
  let logic_and := fun l => my_of_truth (fold_truth my_truth andb3 true3 l) in
  let logic_or := fun l => my_of_truth (fold_truth my_truth orb3 false3 l) in
     ("plus", plus) :: ("+", plus)
  :: ("minus", minus) :: ("-", minus)
  :: ("mult", mult) :: ("*", mult)
  :: ("opp", opp) :: ("neg", opp)
  :: ("/", div) :: ("div", idiv) 
  :: ("%", modulo) :: ("mod", modulo)
  :: ("abs", fun l => match l with
                      | Value_D (Some (q, f, s)) :: nil => 
                        VDec (match Qccompare q (Qc_of_Z 0) with Lt => Qcopp q | _ => q end) f s
                      | v :: nil => my_int_range v (num_fun1 conv num_abs l)
                      | _ => num_fun1 conv num_abs l end)
  :: ("sign", num_fun1 conv num_sign)
  :: ("floor", num_fun1 conv num_floor)
  :: ("ceil", num_fun1 conv num_ceil) :: ("ceiling", num_fun1 conv num_ceil)
  :: ("round", fun l => match l with
                        | Value_D (Some (q, _, _)) :: nil => my_dround false q 0
                        | Value_D (Some (q, _, _)) :: d :: nil => 
                          match z_arg d with Some d => let d := clamp_scale d in my_dround false q d | None => Value_Z None end
                        | v :: nil => num_fun1 conv (fun a => num_round a 0) l
                        | v :: d :: nil => match conv v, z_arg d with
                                           | Some a, Some d => let d := clamp_scale d in my_int_range v (value_of_num (num_round a d)) 
                                           | _, _ => Value_Z None end
                        | _ => Value_Z None end)
  :: ("truncate", fun l => match l with
                           | Value_D (Some (q, _, _)) :: d :: nil => 
                             match z_arg d with Some d => let d := clamp_scale d in my_dround true q d | None => Value_Z None end
                           | v :: d :: nil => match conv v, z_arg d with
                                              | Some a, Some d => let d := clamp_scale d in value_of_num (num_trunc a d) 
                                              | _, _ => Value_Z None end
                           | _ => Value_Z None end)
  :: ("power", num_fun2 conv num_power) :: ("pow", num_fun2 conv num_power)
  (* [ISNULL (x)] is 1 or 0; [INTERVAL (n, n1, n2, ...)] is the number of [ni <= n] for the increasing
     [ni] (the index of the last one), -1 if [n] is NULL ([Item_func_interval]) *)
  :: ("isnull", fun l => match l with v :: nil => Value_Z (Some (if is_null v then 1 else 0)) | _ => Value_Z None end)
  :: ("interval_index", fun l => match l with
                                 | n :: rest => if is_null n then Value_Z (Some (-1))
                                                else Value_Z (Some (Z.of_nat (List.length
                                                       (filter (fun v => negb (is_null v) &&
                                                                         match my_compare_base n v with Some Lt => false | Some _ => true | None => false end)
                                                               rest))))
                                 | nil => Value_Z None end)
  :: ("greatest", extremum_strict is_null my_order is_Gt)
  :: ("least", extremum_strict is_null my_order is_Lt)
  (* conditional expressions *)
  :: ("coalesce", coalesce)
  :: ("ifnull", coalesce)
  :: ("if", fun l => match l with 
                     | c :: a :: b :: nil => match my_truth c with true3 => a | _ => b end
                     | _ => Value_Z None end)
  :: ("nullif", fun l => match l with
                         | v1 :: v2 :: nil => match my_eq3 v1 v2 with
                                              | true3 => default_value (type_of_value v1)
                                              | _ => v1 end
                         | _ => Value_Z None end)
  :: ("case", case_by my_truth)
  (* logic *)
  :: ("and", logic_and) :: ("&&", logic_and)
  :: ("or", logic_or) :: ("||", if ms_pipes_as_concat ss then my_concat else logic_or)
  :: ("xor", fun l => my_of_truth (fold_truth my_truth xor3 false3 l))
  :: ("not", fun l => match l with v :: nil => my_of_truth (negb3 (my_truth v)) | _ => Value_Z None end)
  (* regular expressions (TODO 2.4) *)
  :: ("regexp_like", fun l => match rx_like my_rx false l with
                              | true3 => Value_Z (Some 1) | false3 => Value_Z (Some 0)
                              | _ => match l with
                                     | s :: p :: rest => match rx_setup my_rx s p (opt_val rest 0) with
                                                         | Some None => Value_Err "Illegal argument to a regular expression"
                                                         | _ => Value_Z None end
                                     | _ => Value_Z None end end)
  :: ("regexp_instr", rx_instr my_rx) :: ("regexp_substr", rx_substr my_rx) :: ("regexp_replace", rx_replace my_rx)
  (* strings ([sql/item_strfunc.cc]; TODO 2.2): positions and lengths in characters, [LENGTH] in bytes *)
  :: ("lpad", f_pad my_skit true true) :: ("rpad", f_pad my_skit false true)
  :: ("substring_index", f_substring_index my_skit)
  :: ("insert", f_insert my_skit)
  :: ("space", f_space my_skit)
  :: ("elt", f_elt my_skit)
  :: ("field", f_field my_skit (fun a b => String.eqb (coll_key a) (coll_key b)))
  :: ("find_in_set", f_find_in_set my_skit (fun a b => String.eqb (coll_key a) (coll_key b)))
  :: ("soundex", f_text1 my_skit soundex_cp)
  :: ("trim_both", f_trim_str my_skit 0) :: ("trim_leading", f_trim_str my_skit 1) :: ("trim_trailing", f_trim_str my_skit 2)
  :: ("position", my_locate)
  :: ("md5", f_digest my_skit md5) :: ("sha1", f_digest my_skit sha1) :: ("sha", f_digest my_skit sha1)
  :: ("sha2", f_sha2 my_skit)
  :: ("to_base64", fun l => match texts my_skit l with
                            | Some (s :: nil) => Value_string (Some (to_base64 (bytes_of_string s)))
                            | _ => Value_string None end)
  :: ("from_base64", fun l => match texts my_skit l with
                              | Some (s :: nil) => match from_base64 s with
                                                   | Some b => Value_string (Some (string_of_bytes b))
                                                   | None => Value_string None end
                              | _ => Value_string None end)
  (* [HEX] of a number: the hexadecimal digits of the integer (rounded, as an unsigned 64-bit number) *)
  :: ("hex", fun l => match l with
                      | (Value_string (Some s) | Value_C (Some (s, _))) :: nil => Value_string (Some (hex_of_bytes true (bytes_of_string s)))
                      | v :: nil => match z_arg v with
                                    | Some z => let u := Z.modulo z (2 ^ 64) in
                                                Value_string (Some (match u with 0 => "0"%string | _ =>
                                                  let h := hex_of_bytes true (min_bytes 8 u) in
                                                  match h with String "0"%char r => r | _ => h end end))
                                    | None => Value_string None end
                      | _ => Value_string None end)
  :: ("unhex", fun l => match texts my_skit l with
                        | Some (s :: nil) => match bytes_of_hex s with
                                             | Some b => Value_string (Some (string_of_bytes b))
                                             | None => Value_string None end
                        | _ => Value_string None end)
  :: ("ascii", fun l => match texts my_skit l with
                        | Some (s :: nil) => Value_Z (Some (match bytes_of_string s with b :: _ => b | nil => 0 end))
                        | _ => Value_Z None end)
  :: ("ord", fun l => match texts my_skit l with
                      | Some (s :: nil) => Value_Z (Some (ord_of s))
                      | _ => Value_Z None end)
  :: ("char", fun l => Value_string (Some (string_of_bytes
                         (flat_map (fun v => match z_arg v with Some n => my_char_bytes n | None => nil end) l))))
  :: ("format", fun l => match l with
                         | x :: d :: _ => match lenient x, z_arg d with
                                          | Some n, Some d => Value_string (Some (format_number (match n with Num_Z z => Qc_of_Z z | Num_Q q => q end) d))
                                          | _, _ => Value_string None end
                         | _ => Value_Err "wrong number of arguments" end)
  :: ("octet_length", str1 (fun s => Value_Z (Some (Z.of_nat (String.length s)))))
  :: ("bit_length", str1 (fun s => Value_Z (Some (8 * Z.of_nat (String.length s)))))
  :: ("strcmp", fun l => match l with
                         | a :: b :: nil => match text_of a, text_of b with
                                            | Some a, Some b => Value_Z (Some (match String.compare (coll_key a) (coll_key b) with
                                                                               | Lt => -1 | Eq => 0 | Gt => 1 end))
                                            | _, _ => Value_Z None end
                         | _ => Value_Z None end)
  :: ("concat", my_concat)
  :: ("concat_ws", my_concat_ws)
  :: ("length", str1 (fun s => Value_Z (Some (Z.of_nat (String.length s)))))
  :: ("char_length", str1 (fun s => Value_Z (Some (Z.of_nat (String.length s)))))
  :: ("upper", str_fun1 upper_s) :: ("lower", str_fun1 lower_s)
  :: ("trim", str_fun1 (fun s => string_rtrim (string_ltrim s)))
  :: ("ltrim", str_fun1 string_ltrim) :: ("rtrim", str_fun1 string_rtrim)
  :: ("reverse", str_fun1 string_rev)
  :: ("substring", my_substring) :: ("substr", my_substring) :: ("mid", my_substring)
  :: ("left", fun l => match l with
                       | s :: n :: nil => match text_of s, z_arg n with
                                          | Some s, Some n => Value_string (Some (String.substring 0 (Z.to_nat n) s))
                                          | _, _ => Value_string None end
                       | _ => Value_string None end)
  :: ("right", fun l => match l with
                        | s :: n :: nil => match text_of s, z_arg n with
                                           | Some s, Some n => 
                                             let k := Nat.min (Z.to_nat n) (String.length s) in
                                             Value_string (Some (String.substring (String.length s - k) k s))
                                           | _, _ => Value_string None end
                        | _ => Value_string None end)
  :: ("replace", fun l => match l with
                          | s :: f :: t :: nil => match text_of s, text_of f, text_of t with
                                                  | Some s, Some f, Some t => Value_string (Some (string_replace s f t))
                                                  | _, _, _ => Value_string None end
                          | _ => Value_string None end)
  :: ("repeat", fun l => match l with
                         | s :: n :: nil => match text_of s, z_arg n with
                                            | Some s, Some n => Value_string (Some (string_repeat (Z.to_nat n) s))
                                            | _, _ => Value_string None end
                         | _ => Value_string None end)
  :: ("locate", my_locate)
  :: ("instr", fun l => match l with
                        | s :: sub :: nil => match text_of sub, text_of s with
                                             | Some sub, Some s => Value_Z (Some (coll_index coll sub s))
                                             | _, _ => Value_Z None end
                        | _ => Value_Z None end)
  (* casts *)
  :: ("cast_int", fun l => match l with v :: nil => Value_Z (z_arg v) | _ => Value_Z None end)
  :: ("cast_numeric", fun l => match l with
                               | v :: nil => match lenient v with Some n => Value_Q (Some (Qc_of_num n)) | None => Value_Q None end
                               | _ => Value_Q None end)
  :: ("cast_string", fun l => match l with v :: nil => Value_string (text_of v) | _ => Value_string None end)
  :: ("cast_decimal", fun l => match l with 
                               | v :: p :: s :: nil => match z_arg p, z_arg s with
                                                       | Some p, Some s => my_cast_decimal p s v
                                                       | _, _ => Value_D None end
                               | _ => Value_D None end)
  (* JSON *)
  :: ("json_extract", fun l => match l with d :: p :: nil => my_json_extract d p | _ => Value_J None end)
  (* TODO 2.8: updates by path, removal, arrays, merges, depth, search, overlaps, pretty printing *)
  :: ("json_set", my_json_update true true) :: ("json_insert", my_json_update true false)
  :: ("json_replace", my_json_update false true)
  :: ("json_remove", fun l => my_json_paths (fun p d => match p with nil => None | _ => Some (remove_path p d) end) l)
  :: ("json_array_append", my_json_pathvals (fun p d v => Some (array_append p d v)))
  :: ("json_array_insert", my_json_pathvals (fun p d v => array_insert p d v))
  :: ("json_merge_patch", my_json_docs (fun a b => merge_patch (json_size a + json_size b) a b))
  :: ("json_merge_preserve", my_json_docs (fun a b => merge_preserve (json_size a + json_size b) a b))
  :: ("json_merge", my_json_docs (fun a b => merge_preserve (json_size a + json_size b) a b))
  :: ("json_depth", fun l => match l with
                             | d :: nil => match my_json_doc d with
                                           | Some (Some j) => Value_Z (Some (Z.of_nat (json_depth j)))
                                           | Some None => Value_Z None
                                           | None => Value_Err "Invalid JSON text in argument 1" end
                             | _ => Value_Z None end)
  :: ("json_contains_path", fun l => match l with
                                     | d :: mode :: paths =>
                                       match my_json_doc d, text_of mode with
                                       | Some (Some j), Some m =>
                                         let found := map (fun p => match text_of p with
                                                                    | Some t => match parse_path t with
                                                                                | Some st => match follow st j with Some _ => Some true | None => Some false end
                                                                                | None => None end
                                                                    | None => None end) paths in
                                         if existsb (fun x => match x with None => true | _ => false end) found
                                         then Value_Err "Invalid JSON path expression"
                                         else let bs := map (fun x => match x with Some b => b | None => false end) found in
                                              match Temporal.upper_string m with
                                              | "ONE"%string => Value_Z (Some (if existsb (fun b => b) bs then 1 else 0))
                                              | "ALL"%string => Value_Z (Some (if forallb (fun b => b) bs then 1 else 0))
                                              | _ => Value_Err "The oneOrAll argument may take these values: 'one' or 'all'" end
                                       | Some None, _ => Value_Z None
                                       | None, _ => Value_Err "Invalid JSON text in argument 1"
                                       | _, _ => Value_Z None end
                                     | _ => Value_Z None end)
  :: ("json_search", fun l => match l with
                              | d :: mode :: str :: _ =>
                                match my_json_doc d, text_of mode, text_of str with
                                | Some (Some j), Some m, Some t =>
                                  let ps := search_paths (json_size j) t "$" j in
                                  match Temporal.upper_string m, ps with
                                  | "ONE"%string, nil | "ALL"%string, nil => Value_J None
                                  | "ONE"%string, p :: _ => VJ 0 (JStr p)
                                  | "ALL"%string, p :: nil => VJ 0 (JStr p)
                                  | "ALL"%string, _ => VJ 0 (JArr (map JStr ps))
                                  | _, _ => Value_Err "The oneOrAll argument may take these values: 'one' or 'all'" end
                                | None, _, _ => Value_Err "Invalid JSON text in argument 1"
                                | _, _, _ => Value_J None end
                              | _ => Value_J None end)
  :: ("json_overlaps", fun l => match l with
                                | a :: b :: nil => match my_json_doc a, my_json_doc b with
                                                   | Some (Some x), Some (Some y) => Value_Z (Some (if json_overlaps x y then 1 else 0))
                                                   | None, _ | _, None => Value_Err "Invalid JSON text"
                                                   | _, _ => Value_Z None end
                                | _ => Value_Z None end)
  :: ("json_pretty", fun l => match l with
                              | d :: nil => match my_json_doc d with
                                            | Some (Some j) => Value_string (Some (pretty 2 (normalize j)))
                                            | None => Value_Err "Invalid JSON text in argument 1"
                                            | _ => Value_string None end
                              | _ => Value_string None end)
  :: ("->", fun l => match l with d :: p :: nil => my_json_extract d p | _ => Value_J None end)
  :: ("->>", fun l => match l with d :: p :: nil => my_json_unquote (my_json_extract d p) | _ => Value_string None end)
  :: ("json_unquote", fun l => match l with v :: nil => my_json_unquote v | _ => Value_string None end)
  :: ("json_object", fun l => 
        let fix pairs (l : list value) : option (list (string * json)) :=
            match l with
            | nil => Some nil
            | k :: v :: r => match text_of k, pairs r with
                             | Some key, Some rest => Some ((key, my_json_of_value v) :: rest)
                             | _, _ => None end
            | _ => None end in
        match pairs l with Some ps => VJ 0 (JObj ps) | None => Value_Err "Incorrect parameter count" end)
  :: ("json_array", fun l => VJ 0 (JArr (map my_json_of_value l)))
  (* the argument of [JSON_QUOTE] is a string ("Incorrect type for argument 1 in function json_quote") *)
  :: ("json_quote", fun l => match l with
                             | v :: nil => if is_null v then Value_string None
                                           else match v with
                                                | Value_string (Some t) | Value_C (Some (t, _)) => Value_string (Some (text_compact (JStr t)))
                                                | _ => Value_Err "Incorrect type for argument 1 in function json_quote" end
                             | _ => Value_string None end)
  :: ("json_valid", fun l => match l with 
                             | v :: nil => if is_null v then Value_Z None 
                                           else match v with Value_J _ => Value_Z (Some 1) | _ => 
                                                match text_of v with Some t => Value_Z (Some (match parse_json t with Some _ => 1 | None => 0 end)) | None => Value_Z None end end
                             | _ => Value_Z None end)
  :: ("json_type", fun l => match l with 
                            | v :: nil => match my_json_doc v with Some (Some j) => Value_string (Some (my_json_type_name j)) | Some None => Value_string None | None => Value_Err "Invalid JSON text in argument 1" end
                            | _ => Value_string None end)
  :: ("json_length", fun l => match l with 
                              | v :: nil => match my_json_doc v with Some (Some j) => Value_Z (Some (json_length j)) | Some None => Value_Z None | None => Value_Err "Invalid JSON text in argument 1" end
                              | v :: p :: nil => match my_json_extract v p with Value_J (Some (t, _)) => match parse_json t with Some j => Value_Z (Some (json_length j)) | None => Value_Z None end | Value_Err e => Value_Err e | _ => Value_Z None end
                              | _ => Value_Z None end)
  :: ("json_keys", fun l => match l with 
                            | v :: nil => match my_json_doc v with Some (Some (JObj ms)) => VJ 0 (JArr (map (fun m => JStr (fst m)) (normalize_members ms))) | Some _ => Value_J None | None => Value_Err "Invalid JSON text in argument 1" end
                            | _ => Value_J None end)
  :: ("json_contains", fun l => match l with 
                                | t :: c :: nil => match my_json_doc t, my_json_doc c with
                                                   | Some (Some x), Some (Some y) => Value_Z (Some (if json_contains (json_size x + json_size y) (normalize x) (normalize y) then 1 else 0))
                                                   | Some None, _ | _, Some None => Value_Z None
                                                   | _, _ => Value_Err "Invalid JSON text in argument" end
                                | _ => Value_Z None end)
  (* dates and times *)
  :: ("interval", fun l => match l with
                           | n :: Value_string (Some u) :: nil =>
                             let u := string_map upper_ascii u in
                             match my_unit_parts u with
                             | Some ps => match text_of n with
                                          | Some t => match my_composite_interval ps t with
                                                      | Some (a, b, c) => Value_V (Some (a, b, c))
                                                      | None => Value_V None end
                                          | None => Value_V None end
                             | None =>
                             (* [get_interval_value] of [item_timefunc.cc]: the seconds keep their fraction
                                (truncated to microseconds) when the value is not an integer; the other units take
                                the value as an integer: a decimal is rounded, a string gives the integer which it
                                starts with, a boolean is 0 or 1 *)
                             let frac_sec :=
                                 if String.eqb u "SECOND"
                                 then match n with
                                      | Value_Z _ | Value_I _ | Value_bool _ => None
                                      | _ => match lenient n with
                                             | Some (Num_Q q) => Some (Qc_trunc (Qcmult q (Qc_of_Z 1000000)))
                                             | _ => None end
                                      end
                                 else None in
                             let k := match n with
                                      | Value_string (Some t) => Some (my_int_prefix t)
                                      | Value_bool (Some b) => Some (if b then 1 else 0)%Z
                                      | _ => z_arg n end in
                             match frac_sec with
                             | Some us => Value_V (Some (0, 0, us)%Z)
                             | None =>
                               match k, interval_of_unit 1 u with
                               | Some k, Some (a, b, c) => Value_V (Some (k * a, k * b, k * c))
                               | _, _ => Value_V None end
                             end end
                           | _ => Value_V None end)
  :: ("date_add", fun l => match l with d :: iv :: nil => my_date_add 1 d iv | _ => Value_T None end)
  :: ("date_sub", fun l => match l with d :: iv :: nil => my_date_add (-1) d iv | _ => Value_T None end)
  :: ("adddate", fun l => match l with 
                          | d :: Value_V iv :: nil => my_date_add 1 d (Value_V iv)
                          | d :: n :: nil => match z_arg n with Some k => my_date_add 1 d (Value_V (Some (0, k, 0))) | None => Value_T None end
                          | _ => Value_T None end)
  :: ("subdate", fun l => match l with 
                          | d :: Value_V iv :: nil => my_date_add (-1) d (Value_V iv)
                          | d :: n :: nil => match z_arg n with Some k => my_date_add (-1) d (Value_V (Some (0, k, 0))) | None => Value_T None end
                          | _ => Value_T None end)
  :: ("datediff", fun l => match l with
                           | a :: b :: nil => match my_ts_of a, my_ts_of b with
                                              | Some (x, _), Some (y, _) => Value_Z (Some (ts_days x - ts_days y))
                                              | _, _ => Value_Z None end
                           | _ => Value_Z None end)
  :: ("timestampdiff", fun l => match l with
                                | Value_string (Some u) :: a :: b :: nil => 
                                  match my_ts_of a, my_ts_of b with
                                  | Some (x, _), Some (y, _) => match my_timestampdiff u x y with Some z => Value_Z (Some z) | None => Value_Z None end
                                  | _, _ => Value_Z None end
                                | _ => Value_Z None end)
  :: ("year", fun l => match l with v :: nil => match my_ts_of v with Some (t, _) => let '(y, _, _) := civil_from_days (ts_days t) in Value_Z (Some y) | None => Value_Z None end | _ => Value_Z None end)
  :: ("month", fun l => match l with v :: nil => match my_ts_of v with Some (t, _) => let '(_, m, _) := civil_from_days (ts_days t) in Value_Z (Some m) | None => Value_Z None end | _ => Value_Z None end)
  :: ("day", fun l => match l with v :: nil => match my_ts_of v with Some (t, _) => let '(_, _, d) := civil_from_days (ts_days t) in Value_Z (Some d) | None => Value_Z None end | _ => Value_Z None end)
  :: ("dayofmonth", fun l => match l with v :: nil => match my_ts_of v with Some (t, _) => let '(_, _, d) := civil_from_days (ts_days t) in Value_Z (Some d) | None => Value_Z None end | _ => Value_Z None end)
  :: ("hour", fun l => match l with v :: nil => match my_ts_of v, temporal_parts v with Some (t, _), _ => Value_Z (Some (ts_usec t / 3600000000)) | None, Some (1%nat, u, _) => Value_Z (Some (u / 3600000000)) | _, _ => Value_Z None end | _ => Value_Z None end)
  :: ("minute", fun l => match l with v :: nil => match my_ts_of v, temporal_parts v with Some (t, _), _ => Value_Z (Some ((ts_usec t / 60000000) mod 60)) | None, Some (1%nat, u, _) => Value_Z (Some ((u / 60000000) mod 60)) | _, _ => Value_Z None end | _ => Value_Z None end)
  :: ("second", fun l => match l with v :: nil => match my_ts_of v, temporal_parts v with Some (t, _), _ => Value_Z (Some ((ts_usec t / 1000000) mod 60)) | None, Some (1%nat, u, _) => Value_Z (Some ((u / 1000000) mod 60)) | _, _ => Value_Z None end | _ => Value_Z None end)
  :: ("microsecond", fun l => match l with v :: nil => match my_ts_of v with Some (t, _) => Value_Z (Some (ts_usec t mod 1000000)) | None => Value_Z None end | _ => Value_Z None end)
  :: ("dayofweek", fun l => match l with v :: nil => match my_ts_of v with Some (t, _) => Value_Z (Some (day_of_week (ts_days t) + 1)) | None => Value_Z None end | _ => Value_Z None end)
  :: ("weekday", fun l => match l with v :: nil => match my_ts_of v with Some (t, _) => Value_Z (Some (iso_weekday (ts_days t) - 1)) | None => Value_Z None end | _ => Value_Z None end)
  :: ("dayofyear", fun l => match l with v :: nil => match my_ts_of v with Some (t, _) => Value_Z (Some (day_of_year (ts_days t))) | None => Value_Z None end | _ => Value_Z None end)
  :: ("quarter", fun l => match l with v :: nil => match my_ts_of v with Some (t, _) => let '(_, m, _) := civil_from_days (ts_days t) in Value_Z (Some ((m - 1) / 3 + 1)) | None => Value_Z None end | _ => Value_Z None end)
  :: ("week", fun l => match l with v :: nil => match my_ts_of v with Some (t, _) => Value_Z (Some (my_week0 (ts_days t))) | None => Value_Z None end | _ => Value_Z None end)
  :: ("last_day", fun l => match l with v :: nil => match my_ts_of v with Some (t, _) => let '(y, m, _) := civil_from_days (ts_days t) in VDate (days_from_civil y m (days_in_month y m)) | None => Value_T None end | _ => Value_T None end)
  (* TODO 2.7 *)
  :: ("str_to_date", fun l => match l with
                              | s :: f :: nil => match text_of s, text_of f with
                                                 | Some s, Some f => my_str_to_date s f | _, _ => Value_T None end
                              | _ => Value_T None end)
  :: ("makedate", fun l => match l with
                           | y :: j :: nil => match z_arg y, z_arg j with
                                              | Some y, Some j => if Z.leb j 0 then Value_T None
                                                                  else VDate (days_from_civil (if Z.ltb y 70 then y + 2000 else if Z.ltb y 100 then y + 1900 else y) 1 1 + j - 1)
                                              | _, _ => Value_T None end
                           | _ => Value_T None end)
  :: ("maketime", fun l => match l with
                           | h :: m :: sec :: nil => match z_arg h, z_arg m, lenient sec with
                                                     | Some h, Some m, Some se =>
                                                       if (Z.ltb (m) 0) || (Z.ltb (59) m) then Value_T None
                                                       else let sq := Qc_of_num se in
                                                            let us := Qc_round (Qcmult sq (Qc_of_Z 1000000)) in
                                                            let sgn := if Z.ltb h 0 then -1 else 1 in
                                                            VTime (clamp_time (sgn * ((Z.abs h * 60 + m) * 60 * 1000000 + us))) (match se with Num_Z _ => 0%nat | Num_Q q => Nat.min 6 (qc_scale q) end)
                                                     | _, _, _ => Value_T None end
                           | _ => Value_T None end)
  :: ("sec_to_time", fun l => match l with
                              | v :: nil => match lenient v with
                                            | Some n => let q := Qc_of_num n in
                                                        VTime (clamp_time (Qc_round (Qcmult q (Qc_of_Z 1000000)))) (match n with Num_Z _ => 0%nat | Num_Q q => Nat.min 6 (qc_scale q) end)
                                            | None => Value_T None end
                              | _ => Value_T None end)
  :: ("time_to_sec", fun l => match l with
                              | v :: nil => match temporal_parts v with
                                            | Some (1%nat, us, _) => Value_Z (Some (Z.quot us 1000000))
                                            | _ => match my_ts_of v with Some (t, _) => Value_Z (Some (ts_usec t / 1000000)) | None => Value_Z None end end
                              | _ => Value_Z None end)
  :: ("from_days", fun l => match l with v :: nil => match z_arg v with Some n => my_from_days n | None => Value_T None end | _ => Value_T None end)
  :: ("from_unixtime", fun l => match l with
                                | v :: rest => match lenient v with
                                               | Some n => let q := Qc_of_num n in
                                                           if Qc_lt_bool q (Qc_of_Z 0) then Value_T None
                                                           else let t := ts_of (days_from_civil 1970 1 1) 0 + Qc_round (Qcmult q (Qc_of_Z 1000000)) in
                                                                match rest with
                                                                | nil => VTs t (match n with Num_Z _ => 0%nat | Num_Q q => Nat.min 6 (qc_scale q) end)
                                                                | f :: nil => match text_of f with
                                                                              | Some f => Value_string (Some (my_format (S (String.length f)) t f))
                                                                              | None => Value_string None end
                                                                | _ => Value_T None end
                                               | None => Value_T None end
                                | _ => Value_T None end)
  :: ("dayname", fun l => match l with v :: nil => match my_ts_of v with
                                                   | Some (t, _) => Value_string (Some (day_name (day_of_week (ts_days t)))) | None => Value_string None end
                                     | _ => Value_string None end)
  :: ("monthname", fun l => match l with v :: nil => match my_ts_of v with
                                                     | Some (t, _) => let '(_, m, _) := civil_from_days (ts_days t) in Value_string (Some (month_name m))
                                                     | None => Value_string None end
                                       | _ => Value_string None end)
  :: ("period_add", fun l => match l with
                             | p :: n :: nil => match z_arg p, z_arg n with
                                                | Some p, Some n => Value_Z (Some (if Z.eqb p 0 then 0 else months_period (period_months p + n)))
                                                | _, _ => Value_Z None end
                             | _ => Value_Z None end)
  :: ("period_diff", fun l => match l with
                              | a :: b :: nil => match z_arg a, z_arg b with
                                                 | Some a, Some b => Value_Z (Some (period_months a - period_months b))
                                                 | _, _ => Value_Z None end
                              | _ => Value_Z None end)
  :: ("timediff", fun l => match l with
                           | a :: b :: nil => match temporal_parts a, temporal_parts b with
                                              | Some (1%nat, x, f1), Some (1%nat, y, f2) => VTime (clamp_time (x - y)) (Nat.max f1 f2)
                                              | _, _ => match my_ts_of a, my_ts_of b with
                                                        | Some (x, _), Some (y, _) => VTime (clamp_time (x - y)) 6
                                                        | _, _ => Value_T None end end
                           | _ => Value_T None end)
  :: ("addtime", fun l => match l with
                          | a :: b :: nil => match temporal_parts b with
                                             | Some (1%nat, d, _) => match temporal_parts a with
                                                                    | Some (1%nat, x, f) => VTime (clamp_time (x + d)) f
                                                                    | _ => match my_ts_of a with Some (x, _) => VTs (x + d) 6 | None => Value_T None end end
                                             | _ => Value_T None end
                          | _ => Value_T None end)
  :: ("subtime", fun l => match l with
                          | a :: b :: nil => match temporal_parts b with
                                             | Some (1%nat, d, _) => match temporal_parts a with
                                                                    | Some (1%nat, x, f) => VTime (clamp_time (x - d)) f
                                                                    | _ => match my_ts_of a with Some (x, _) => VTs (x - d) 6 | None => Value_T None end end
                                             | _ => Value_T None end
                          | _ => Value_T None end)
  :: ("time_format", fun l => match l with
                              | v :: f :: nil => match temporal_parts v, text_of f with
                                                 | Some (1%nat, us, _), Some f => Value_string (Some (time_format us f))
                                                 | _, Some f => match my_ts_of v with Some (t, _) => Value_string (Some (time_format (ts_usec t) f)) | None => Value_string None end
                                                 | _, _ => Value_string None end
                              | _ => Value_string None end)
  :: ("utc_date", fun _ => VDate (ts_days statement_time))
  :: ("utc_time", fun _ => VTime (ts_usec statement_time) 0)
  :: ("utc_timestamp", fun _ => VTs statement_time 0)
  :: ("extract", fun l => match l with
                          | u :: v :: nil => match text_of u, my_ts_of v with
                                             | Some u, Some (t, _) => match my_extract (Temporal.upper_string u) t with
                                                                      | Some z => Value_Z (Some z) | None => Value_Z None end
                                             | _, _ => Value_Z None end
                          | _ => Value_Z None end)
  :: ("to_days", fun l => match l with v :: nil => match my_ts_of v with Some (t, _) => Value_Z (Some (ts_days t + 719528)) | None => Value_Z None end | _ => Value_Z None end)
  :: ("date", fun l => match l with v :: nil => match my_ts_of v with Some (t, _) => VDate (ts_days t) | None => Value_T None end | _ => Value_T None end)
  :: ("date_format", fun l => match l with
                              | v :: f :: nil => match my_ts_of v, text_of f with
                                                 | Some (t, _), Some fmt => Value_string (Some (my_format (S (String.length fmt)) t fmt))
                                                 | _, _ => Value_string None end
                              | _ => Value_string None end)
  :: ("unix_timestamp", fun l => match l with 
                                 | nil => Value_Z (Some (statement_time / 1000000))
                                 | v :: nil => match my_ts_of v with Some (t, _) => Value_Z (Some (t / 1000000)) | None => Value_Z None end
                                 | _ => Value_Z None end)
  (* the time of the statement ([Temporal.statement_time]) *)
  :: ("now", fun _ => VTs statement_time 0) :: ("current_timestamp", fun _ => VTs statement_time 0)
  :: ("sysdate", fun _ => VTs statement_time 0) :: ("localtimestamp", fun _ => VTs statement_time 0)
  :: ("curdate", fun _ => VDate (ts_days statement_time)) :: ("current_date", fun _ => VDate (ts_days statement_time))
  :: ("curtime", fun _ => VTime (ts_usec statement_time) 0) :: ("current_time", fun _ => VTime (ts_usec statement_time) 0)
  :: ("cast_date", fun l => match l with v :: nil => my_cast_temporal 0 v | _ => Value_T None end)
  :: ("cast_time", fun l => match l with v :: nil => my_cast_temporal 1 v | _ => Value_T None end)
  :: ("cast_datetime", fun l => match l with v :: nil => my_cast_temporal 2 v | _ => Value_T None end)
  :: ("lit_datetime", fun l => match l with v :: nil => my_lit_datetime v | _ => Value_T None end)
  :: ("lit_time", fun l => match l with v :: nil => my_lit_time v | _ => Value_T None end)
  :: ("cast_timestamp", fun l => match l with v :: nil => my_cast_temporal 2 v | _ => Value_T None end)
  (* [s COLLATE c]: an unknown collation is an error ([ER_UNKNOWN_COLLATION]) *)
  :: ("collate", fun l => match l with
                          | v :: Value_string (Some n) :: nil =>
                            match my_collation_of_name n, text_of v with
                            | Some _, Some s => Value_C (Some (s, n))
                            | Some _, None => Value_string None
                            | None, _ => Value_Err "Unknown collation"
                            end
                          | _ => Value_string None end)
  (* [CAST(x AS UNSIGNED)]: the value modulo 2^64 ([Item_func_unsigned]) *)
  :: ("cast_unsigned", fun l => match l with 
                                | v :: nil => match z_arg v with 
                                              | Some z => Value_I (Some (Z.modulo z 18446744073709551616, 1%nat)) 
                                              | None => Value_I None end
                                | _ => Value_I None end)
  :: ("cast_double", fun l => match l with v :: nil => my_double (match lenient v with Some n => value_of_num n | None => Value_Q None end) | _ => Value_F None end)
  :: nil.

(** For a floating-point argument, the mathematical functions return a double: "for string or
    floating-point arguments, the return value has a floating-point type" (MySQL manual, [FLOOR],
    [ROUND], ...) *)
Definition my_float_funs : list string :=
  "abs" :: "floor" :: "ceil" :: "ceiling" :: "round" :: "truncate" :: "power" :: "pow" :: "opp" :: "neg" :: "%" :: "mod"
  :: "sqrt" :: "exp" :: "ln" :: "log" :: "log2" :: "log10" :: "sin" :: "cos" :: "tan" :: "cot" :: "asin" :: "acos"
  :: "atan" :: "atan2" :: "degrees" :: "radians" :: nil.

(** the decimals of the result of a function on doubles: [FLOOR] and [CEIL] have none, [ROUND(x, d)] [d],
    the arithmetic those of [Item_func_additive_op], [Item_func_mul], [Item_func_div] *)
Definition my_float_dec (f : string) (l : list value) : option nat :=
  match f, l with
  | ("floor" | "ceil" | "ceiling"), _ => Some 0%nat
  | "round", _ :: d :: nil => match z_arg d with Some k => Some (Z.to_nat (Z.max 0 k)) | None => None end
  | "round", _ :: nil => Some 0%nat
  | "truncate", _ :: d :: nil => match z_arg d with Some k => Some (Z.to_nat (Z.max 0 k)) | None => None end
  | ("+" | "-" | "plus" | "minus"), a :: b :: nil => dec_max (my_fdec a) (my_fdec b)
  | ("*" | "mult"), a :: b :: nil => dec_sum (my_fdec a) (my_fdec b)
  | ("abs" | "opp" | "neg"), a :: nil => my_fdec a
  | _, _ => None
  end%string.

Definition my_symbol_table : list (string * (list value -> value)) :=
  map (fun p => if existsb (String.eqb (fst p)) my_float_funs
                then (fst p, fun l => 
                        (* a date or a time is a number; with a double, the result is a double *)
                        let l' := map (fun v => match my_temporal_number v with 
                                                | Some (q, _) => my_double (Value_Q (Some q)) | None => v end) l in
                        if existsb is_F l' then with_fdec (my_float_dec (fst p) l') (my_double ((snd p) l')) else (snd p) l')
                else if existsb (String.eqb (fst p)) ("+" :: "-" :: "*" :: "plus" :: "minus" :: "mult" :: nil)
                then (fst p, fun l => let r := (snd p) l in if is_F r then with_fdec (my_float_dec (fst p) l) r else r)
                else p) (c_math_table false lenient ++ bit_table false lenient ++ ("rand", my_rand lenient) :: my_symbol_table_raw).

(** MariaDB: the variance and the standard deviation have the decimals of their argument plus 4, at most 30
    ([Item_sum_variance::fix_length_and_dec]: [MY_MIN (args[0]->decimals + 4, FLOATING_POINT_DECIMALS)], 31
    being not fixed); MySQL prints them with no fixed decimals *)
Definition var_dec (f : list value -> value) (l : list value) : value :=
  if Nat.eqb (ms_regex ss) 1
  then match filter (fun v => negb (is_null v)) l with
       | v :: _ => match my_fdec v with
                   | Some d => if Nat.ltb (d + 4) 31 then with_fdec (Some (d + 4)%nat) (f l) else f l
                   | None => f l end
       | nil => f l end
  else f l.

Definition my_aggregate_table : list (string * (list value -> value)) :=
     ("count", agg_count_by is_null)
  :: ("count(*)", fun l => Value_Z (Some (Z.of_nat (List.length l))))
  :: ("sum", my_agg_sum is_null)
  :: ("avg", my_agg_avg div_precision_increment is_null)
  :: ("min", agg_extremum_by is_null my_order is_Lt)
  :: ("max", agg_extremum_by is_null my_order is_Gt)
  :: ("group_concat", fun l => truncate_text (ms_group_concat_max_len ss) (agg_concat_by is_null "," l))
  :: ("group_concat_sep", fun l => truncate_text (ms_group_concat_max_len ss) (agg_concat_sep_by is_null "," l))
  (* [BIT_AND], [BIT_OR], [BIT_XOR]: [BIGINT UNSIGNED]; on the empty group, all ones for [BIT_AND] and 0
     for the others ([Item_sum_bit]) *)
  :: ("bit_and", fun l => match agg_bit_by is_null (fun a b => Z.land (Z.modulo a (2 ^ 64)) (Z.modulo b (2 ^ 64))) l with
                          | Value_Z (Some z) => Value_I (Some (Z.modulo z (2 ^ 64), 1%nat))
                          | _ => Value_I (Some (2 ^ 64 - 1, 1%nat)) end)
  :: ("bit_or", fun l => match agg_bit_by is_null (fun a b => Z.lor (Z.modulo a (2 ^ 64)) (Z.modulo b (2 ^ 64))) l with
                         | Value_Z (Some z) => Value_I (Some (Z.modulo z (2 ^ 64), 1%nat))
                         | _ => Value_I (Some (0, 1%nat)) end)
  :: ("bit_xor", bit_xor_agg true is_null lenient)
  (* the variance and the standard deviation are [DOUBLE]; [VARIANCE], [STD] and [STDDEV] are the
     population ones *)
  :: ("var_pop", var_dec (my_var_agg false false is_null lenient))
  :: ("variance", var_dec (my_var_agg false false is_null lenient))
  :: ("var_samp", var_dec (my_var_agg true false is_null lenient))
  :: ("std", var_dec (my_var_agg false true is_null lenient)) :: ("stddev", var_dec (my_var_agg false true is_null lenient))
  :: ("stddev_pop", var_dec (my_var_agg false true is_null lenient))
  :: ("stddev_samp", var_dec (my_var_agg true true is_null lenient))
  :: ("json_arrayagg", json_array_agg 0 my_json_of_value)
  :: ("json_objectagg", json_object_agg 0 is_null text_of my_json_of_value)
  :: ("count_distinct2", count_distinct2 is_null (fun a b => match my_compare_base a b with Some Eq => true | _ => false end))
  :: nil.

(** The constructs of MySQL 8.0 (8.0.31 and later for [INTERSECT] and [EXCEPT]). *)
(** The type of a column of a set operation ([Item_type_holder]): with a [DECIMAL] value and no double or
    string, the column is a [DECIMAL] with the largest scale of its values, and every value (integers
    too) is shown with that scale (TODO 3.3) *)
Definition my_unify_column (l : list value) : list value :=
  let is_str v := match v with Value_string (Some _) | Value_C (Some _) => true | _ => false end in
  if existsb is_D l && negb (existsb (fun v => is_F v || is_str v) l) then
    let sc := fold_left (fun acc v => match v with Value_D (Some (_, _, s)) => Nat.max acc s | _ => acc end) l 0%nat in
    map (fun v => match v with
                  | Value_D (Some (q, _, _)) => VDec q sc sc
                  | Value_Z (Some z) | Value_I (Some (z, _)) => VDec (Qc_of_Z z) sc sc
                  | _ => v end) l
  else l.

(** [JSON_TABLE (doc, rowpath COLUMNS (c1 ... PATH p1, ...))] as [json_table (doc, rowpath, p1, ...)]: the
    rows are the values at [rowpath], a path whose last step may be [[*]] (every element of an array);
    a column is the value at its path from the row (a scalar, its SQL value; NULL when missing). The
    declared types of the columns and the [ON EMPTY] / [ON ERROR] clauses are not modelled (TODO 3.4). *)
Definition my_json_table (l : list value) : list (list value) :=
  match l with
  | d :: rp :: cols =>
    match my_json_doc d, text_of rp with
    | Some (Some j), Some rpath =>
      let n := String.length rpath in
      let (base, star) := if Nat.leb 3 n && String.eqb (substring (n - 3) 3 rpath) "[*]"
                          then (substring 0 (n - 3) rpath, true) else (rpath, false) in
      match parse_path base with
      | Some st =>
        let rows := match follow st j with
                    | Some (JArr xs) => if star then xs else JArr xs :: nil
                    | Some x => if star then nil else x :: nil
                    | None => nil end in
        let colv (r : json) (c : value) :=
            match text_of c with
            | Some cp => match parse_path cp with
                         | Some cst => match follow cst r with
                                       | Some JNull | None => Value_Z None
                                       | Some (JStr t) => Value_string (Some t)
                                       | Some x => json_scalar (VJ 0 x)
                                       end
                         | None => Value_Err "Invalid JSON path expression" end
            | None => Value_Z None end in
        map (fun r => map (colv r) cols) rows
      | None => (Value_Err "Invalid JSON path expression" :: nil) :: nil
      end
    | Some None, _ => nil
    | _, _ => (Value_Err "Invalid JSON text in argument 1" :: nil) :: nil
    end
  | _ => nil
  end%string.

Definition my_table_funs (name : string) : option (list value -> list (list value)) :=
  match name with
  | "json_table" => Some my_json_table
  | _ => None
  end%string.

Definition my_supports (f : feature) : bool :=
  match f with
  | F_Full_Join | F_Frame_Groups | F_Filter_Agg | F_Nulls_Order => false
  (* no [EXCLUDE] in frames; [RESPECT NULLS] and [FROM FIRST] only *)
  | F_Frame_Exclusion | F_Null_Treatment | F_From_Last | F_Rec_Aggregate | F_Group_Aggregate | F_Frame_Bounds | F_Ntile_Zero => false
  (* [ONLY_FULL_GROUP_BY] is in the default [sql_mode]; functional dependencies are not modelled *)
  | F_Fetch_Ties | F_Fetch_Percent => false
  (* only [WITH ROLLUP] *)
  | F_Grouping_Sets | F_Cube => false
  | _ => true
  end.

Definition canon_my (v : value) : value :=
  match v with
  | Value_string (Some s) => Value_string (Some (coll_key s))
  | Value_C (Some (s, n)) => 
    Value_string (Some (match my_collation_of_name n with
                        | Some (c, p) => Collation.coll_key c p s
                        | None => s end))
  | Value_bool (Some b) => Value_Q (Some (Qc_of_Z (if b then 1 else 0)))
  | _ => canon_numeric v
  end.

(** ** Functions added by the closeout of the MySQL family (TODO 4.2) *)
Local Open Scope Z_scope.

(** the digits of [z] (non-negative) in base [b] (2 to 36), in upper case *)
Definition my_digits (b z : Z) : string :=
  let fix go (fuel : nat) (z : Z) (acc : string) :=
      match fuel with
      | O => acc
      | S f => let d := Z.modulo z b in
               let acc := String (Ascii.ascii_of_nat (Z.to_nat (if Z.ltb d 10 then 48 + d else 55 + d))) acc in
               if Z.ltb z b then acc else go f (Z.div z b) acc
      end in
  go 70%nat z EmptyString.

(** the value of the longest prefix of [s] which is a number in base [b] (and its sign) *)
Definition my_parse_base (b : Z) (s : string) : Z :=
  let digit (c : Ascii.ascii) : option Z :=
      let n := Z.of_nat (Ascii.nat_of_ascii c) in
      let d := if (48 <=? n) && (n <=? 57) then n - 48
               else if (65 <=? n) && (n <=? 90) then n - 55
               else if (97 <=? n) && (n <=? 122) then n - 87 else 99 in
      if d <? b then Some d else None in
  let fix go (s : string) (acc : Z) :=
      match s with
      | String c r => match digit c with Some d => go r (acc * b + d) | None => acc end
      | EmptyString => acc
      end in
  let fix ltrim (s : string) := match s with String " "%char r => ltrim r | _ => s end in
  let s := ltrim s in
  match s with
  | String "-"%char r => - go r 0
  | String "+"%char r => go r 0
  | _ => go s 0
  end.

(** [CONV (n, from, to)]: unsigned 64-bit arithmetic; a negative [to] gives a signed result *)
Definition my_conv (l : list value) : value :=
  match l with
  | v :: f :: t :: nil =>
    match text_of v, z_arg f, z_arg t with
    | Some s, Some fb, Some tb =>
      let fb' := Z.abs fb in let tb' := Z.abs tb in
      if (fb' <? 2) || (36 <? fb') || (tb' <? 2) || (36 <? tb') then Value_string None
      else let n := Z.modulo (my_parse_base fb' s) (2 ^ 64) in
           if (tb <? 0) && (2 ^ 63 <=? n) then Value_string (Some ("-" ++ my_digits tb' (2 ^ 64 - n)))
           else Value_string (Some (my_digits tb' n))
    | _, _, _ => Value_string None
    end
  | _ => Value_Err "wrong number of arguments"
  end.

(** CRC-32 (ISO 3309, polynomial [0xEDB88320] reflected) of the bytes of a string *)
Definition crc32_byte (crc : Z) (b : Z) : Z :=
  let fix bits (n : nat) (c : Z) :=
      match n with O => c | S m => bits m (if Z.odd c then Z.lxor (Z.shiftr c 1) 3988292384 else Z.shiftr c 1) end in
  bits 8%nat (Z.lxor crc b).
Definition crc32_string (s : string) : Z :=
  let fix go (s : string) (c : Z) :=
      match s with String a r => go r (crc32_byte c (Z.of_nat (Ascii.nat_of_ascii a))) | EmptyString => c end in
  Z.lxor (go s 4294967295) 4294967295.

(** [INET_ATON]: [a.b.c.d], or fewer parts (the last one is the low byte: ['127.1'] is [127.0.0.1]) *)
Definition my_inet_parts (s : string) : option (list Z) :=
  let fix go (s : string) (cur : option Z) (acc : list Z) :=
      match s with
      | EmptyString => match cur with Some z => Some (rev (z :: acc)) | None => None end
      | String "."%char r => match cur with Some z => go r None (z :: acc) | None => None end
      | String c r => let n := Z.of_nat (Ascii.nat_of_ascii c) in
                      if (48 <=? n) && (n <=? 57)
                      then go r (Some (match cur with Some z => z * 10 | None => 0 end + (n - 48))) acc
                      else None
      end in
  match go s None nil with
  | Some ps => if (Nat.leb (List.length ps) 4) && forallb (fun z => z <=? 255) ps then Some ps else None
  | None => None
  end.
Definition my_inet_aton (s : string) : option Z :=
  match my_inet_parts s with
  | Some ps => let n := List.length ps in
               let hi := firstn (n - 1) ps in
               let lo := last ps 0 in
               Some (fst (fold_left (fun (acc : Z * Z) z => (fst acc + z * 2 ^ (8 * snd acc), snd acc - 1)) hi
                                    (0, 3)) + lo)
  | None => None
  end.

Definition my_quote (s : string) : string :=
  let fix go (s : string) :=
      match s with
      | EmptyString => EmptyString
      | String c r => let n := Ascii.nat_of_ascii c in
                      if Nat.eqb n 39 || Nat.eqb n 92 then String "\"%char (String c (go r))
                      else if Nat.eqb n 0 then String "\"%char (String "0"%char (go r))
                      else if Nat.eqb n 26 then String "\"%char (String "Z"%char (go r))
                      else String c (go r)
      end in
  "'" ++ go s ++ "'".

Definition my_closeout_funs : list (string * (list value -> value)) :=
  ("conv", my_conv)
  :: ("bin", fun l => match l with v :: nil => my_conv (v :: Value_Z (Some 10) :: Value_Z (Some 2) :: nil)
                                 | _ => Value_Err "wrong number of arguments" end)
  :: ("oct", fun l => match l with v :: nil => my_conv (v :: Value_Z (Some 10) :: Value_Z (Some 8) :: nil)
                                 | _ => Value_Err "wrong number of arguments" end)
  :: ("crc32", fun l => match l with v :: nil => match text_of v with
                                                 | Some s => VInt 0 (crc32_string s) | None => Value_I None end
                                   | _ => Value_Err "wrong number of arguments" end)
  :: ("inet_aton", fun l => match l with v :: nil => match text_of v with
                                                     | Some s => match my_inet_aton s with Some z => VInt 0 z | None => Value_I None end
                                                     | None => Value_I None end
                                       | _ => Value_Err "wrong number of arguments" end)
  :: ("inet_ntoa", fun l => match l with v :: nil => match z_arg v with
                                                     | Some z => if (z <? 0) || (2 ^ 32 <=? z) then Value_string None
                                                                 else Value_string (Some (string_of_Z (z / 2 ^ 24) ++ "." ++ string_of_Z (Z.modulo (z / 2 ^ 16) 256) ++ "." ++
                                                                                         string_of_Z (Z.modulo (z / 256) 256) ++ "." ++ string_of_Z (Z.modulo z 256)))
                                                     | None => Value_string None end
                                       | _ => Value_Err "wrong number of arguments" end)
  :: ("is_ipv4", fun l => match l with v :: nil => match text_of v with
                                                   | Some s => match my_inet_parts s with
                                                               | Some ps => Value_Z (Some (if Nat.eqb (List.length ps) 4 then 1 else 0))
                                                               | None => Value_Z (Some 0) end
                                                   | None => Value_Z (Some 0) end
                                     | _ => Value_Err "wrong number of arguments" end)
  :: ("quote", fun l => match l with v :: nil => match text_of v with
                                                 | Some s => Value_string (Some (my_quote s))
                                                 | None => Value_string (Some "NULL") end
                                   | _ => Value_Err "wrong number of arguments" end)
  (* [WEEKOFYEAR (d)] is [WEEK (d, 3)]: the ISO 8601 week *)
  :: ("weekofyear", fun l => match l with
                             | v :: nil => match my_ts_of v with Some (t, _) => Value_Z (Some (snd (iso_week_year (ts_days t))))
                                                                 | None => Value_Z None end
                             | _ => Value_Err "wrong number of arguments" end)
  :: ("any_value", fun l => match l with v :: nil => v | _ => Value_Err "wrong number of arguments" end)
  :: ("make_set", fun l => match l with
                           | b :: ss => match z_arg b with
                                        | Some z => let z := Z.modulo z (2 ^ 64) in
                                                    let picked := flat_map (fun p => let '(i, v) := p in
                                                                    if Z.testbit z (Z.of_nat i) then
                                                                      match text_of v with Some t => t :: nil | None => nil end
                                                                    else nil) (combine (seq 0 (List.length ss)) ss) in
                                                    Value_string (Some (String.concat "," picked))
                                        | None => Value_string None end
                           | nil => Value_Err "wrong number of arguments" end)
  :: ("export_set", fun l =>
        match l with
        | b :: on :: off :: rest =>
          let sep := match rest with s :: _ => text_of s | nil => Some "," end in
          let n := match rest with _ :: k :: _ => z_arg k | _ => Some 64 end in
          match z_arg b, text_of on, text_of off, sep, n with
          | Some z, Some o, Some f, Some sp, Some k =>
            let k := if (k <? 0) || (64 <? k) then 64 else k in
            let z := Z.modulo z (2 ^ 64) in
            Value_string (Some (String.concat sp (map (fun i => if Z.testbit z (Z.of_nat i) then o else f) (seq 0 (Z.to_nat k)))))
          | _, _, _, _, _ => Value_string None
          end
        | _ => Value_Err "wrong number of arguments" end)
  :: nil.

Local Open Scope string_scope.
Definition my_aliases : list (string * string) :=
  ("character_length", "char_length") :: ("lcase", "lower") :: ("ucase", "upper") :: ("time", "cast_time")
  :: ("timestamp_diff", "timestampdiff") :: ("localtime", "now") :: ("localtimestamp", "now") :: nil.
Definition with_my_aliases (t : list (string * (list value -> value))) : list (string * (list value -> value)) :=
  t ++ flat_map (fun p => match string_assoc _ (snd p) t with Some f => (fst p, f) :: nil | None => nil end) my_aliases
    (* [TIMESTAMP (e)] is [CAST (e AS DATETIME)] *)
    ++ match string_assoc _ "cast_datetime" t with
       | Some f => ("timestamp", fun l => match l with d :: nil => f (d :: nil)
                                                    | _ => Value_Err "wrong number of arguments" end) :: nil
       | None => nil end.

Definition mysql_vs (name : string) (supports : feature -> bool) : vsem :=
  mk_vsem name
          (table_of_list (like_table my_skit true (rep_of (ms_coll ss)) (rep_of (ms_coll ss)) (Some 92)
                          ++ ("regexp", rx_like my_rx false) :: ("not regexp", fun l => negb3 (rx_like my_rx false l))
                          :: my_pred_table))
          (table_of_list (with_my_aliases (sys_table default_env name ++ my_closeout_funs ++ my_symbol_table)))
          (table_of_list my_aggregate_table)
          is_null
          my_truth
          my_of_truth
          my_eq3
          my_order
          canon_my
          true
          (* [ONLY_FULL_GROUP_BY] also rejects a [SELECT DISTINCT] ordered by an expression which is not selected
             ([ER_FIELD_IN_ORDER_NOT_SELECT]) *)
          (fun f => match f with F_Bare_Column | F_Order_Not_Selected => negb (ms_only_full_group_by ss) | _ => supports f end)
          false
          (* [Illegal mix of collations]: a comparison of two strings with different explicit collations *)
          (fun p l => match l with
                      | Value_C (Some (_, n1)) :: Value_C (Some (_, n2)) :: _ => 
                        negb (String.eqb n1 n2) && existsb (String.eqb p) ("=" :: "<>" :: "!=" :: "<" :: "<=" :: ">" :: ">=" :: "<=>" :: nil)
                      | _ => bad_escape my_skit p l || rx_bad my_rx ("regexp" :: "not regexp" :: nil)%string p l end)
          (* an integer literal is a [BIGINT], a [BIGINT UNSIGNED] above 2^63 - 1, a [DECIMAL] above 2^64 - 1 *)
          (fun v => match v with
                    | Value_Z (Some z) => if int_range_ok 64 z then v 
                                          else if int_range_ok 1 z then Value_I (Some (z, 1%nat))
                                          else VDec (Qc_of_Z z) 0 0
                    | _ => v end)
          (fun _ => false)
          (fun _ _ l => l)
          my_unify_column
          my_table_funs.

End Session.

(** MySQL 8 with its default collation [utf8mb4_0900_ai_ci] (no padding). *)
(** The default session of MySQL 8.0 and 8.4: [sql_mode] is [ONLY_FULL_GROUP_BY, STRICT_TRANS_TABLES,
    NO_ZERO_IN_DATE, NO_ZERO_DATE, ERROR_FOR_DIVISION_BY_ZERO, NO_ENGINE_SUBSTITUTION],
    [group_concat_max_len] is 1024. *)
Definition my_default_session : my_session := mk_my_session false Coll_UCA900_AI_CI 4 false true 1024%N 0.

Definition MySQL : vsem := mysql_vs my_default_session "MySQL" my_supports.
