(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**                          The PostgreSQL dialect                                 *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String Ascii ZArith NArith QArith Qcanon.

Require Import Bool3 OrderedSet SqlFull Temporal Json Values Dialects ValueKit Collation Hash StringFuns Regex RegexFuns Aggregates TemporalFuns JsonFuns SystemFuns.

Close Scope Q_scope.
Close Scope Qc_scope.
Open Scope string_scope.

Import NullValues.

(** The key of a value: all the NULLs are the same, and the numbers are compared as
    exact numerics, whatever their declared type. *)
Definition canon_numeric (v : value) : value :=
  match v with
  | Value_Z (Some z) => Value_Q (Some (Qc_of_Z z))
  | Value_I (Some (z, _)) => Value_Q (Some (Qc_of_Z z))
  (* [1.50] and [1.5] are not distinct: the scale is not part of the identity of a decimal *)
  | Value_D (Some (q, _, _)) => Value_Q (Some q)
  (* a finite float, or -0, is identified with the number it stands for *)
  | Value_F (Some (q, k)) => if Nat.leb (Nat.div (Nat.modulo k 10) 2) 1 then Value_Q (Some q) else Value_F (Some (q, (2 * Nat.div (Nat.modulo k 10) 2)%nat))
  | _ => if is_null v then Value_Z None else v
  end.

(** PostgreSQL:
    - strict typing: values of different types are not comparable (here the comparison
      is UNKNOWN, where PostgreSQL signals a type error);
    - conditions are booleans;
    - strings are compared byte by byte (the default deterministic collation);
    - NULLs are the largest values of [ORDER BY];
    - [/] on integers is the integer division, truncated towards zero; a division by zero
      is an error (here NULL);
    - [||] is the concatenation, and NULL if one of the operands is NULL; [concat]
      ignores NULLs;
    - [greatest] and [least] ignore NULLs;
    - [avg] of integers is an exact numeric, [sum] of the empty set is NULL.
    The tables are those of [Values.v]. *)
(** ** The string functions (TODO 2.2, [src/backend/utils/adt/varlena.c], [oracle_compat.c], [quote.c])

    The positions and lengths count characters. [lpad]/[rpad] cut a longer string and leave it when the
    padding is empty; [split_part] counts from the end for a negative position (PostgreSQL 14); [chr (0)] is
    an error; [to_hex] writes the two's complement of the integer in its width. *)
Definition pg_skit : skit :=
  mk_skit (fun v => match v with Value_C (Some (s, _)) => Some s | _ => text_of v end)
          (fun v => match int_parts v with Some (z, _) => Some z | None => None end)
          (fun s => Value_string (Some s)) (Value_string None).

Definition pg_string_table : list (string * (list value -> value)) :=
  let k := pg_skit in
     ("lpad", f_pad k true false) :: ("rpad", f_pad k false false)
  :: ("split_part", f_split_part k) :: ("translate", f_translate k)
  :: ("initcap", f_text1 k initcap_cp)
  :: ("overlay", f_overlay k)
  :: ("strpos", f_strpos k)
  :: ("position", fun l => match l with a :: b :: nil => f_strpos k (b :: a :: nil) | _ => Value_Err "wrong number of arguments" end)
  :: ("btrim", f_trim_set k 0) :: ("ltrim", f_trim_set k 1) :: ("rtrim", f_trim_set k 2)
  :: ("trim_both", f_trim_set k 0) :: ("trim_leading", f_trim_set k 1) :: ("trim_trailing", f_trim_set k 2)
  :: ("concat_ws", f_concat_ws k)
  :: ("md5", f_digest k md5)
  :: ("quote_literal", f_text1 k quote_literal_cp)
  :: ("quote_ident", f_text1 k quote_ident_cp)
  :: ("format", fun l => match l with
                         | f :: args => match sk_txt k f with
                                        | Some f => match pg_format_string (cps f) (map (fun v => option_map cps (sk_txt k v)) args) with
                                                    | Some r => ret_cp k r
                                                    | None => Value_Err "unrecognized format() type specifier"
                                                    end
                                        | None => Value_string None end
                         | nil => Value_Err "wrong number of arguments" end)
  :: ("ascii", fun l => match texts k l with
                        | Some (s :: nil) => Value_I (Some (match cps s with c :: _ => c | nil => 0 end, 32%nat))
                        | Some _ => Value_Err "wrong number of arguments"
                        | None => Value_I None end)
  :: ("chr", fun l => match l with
                      | v :: nil => match sk_int k v with
                                    | Some n => if Z.eqb n 0 then Value_Err "null character not permitted"
                                                else if Z.ltb n 0 then Value_Err "character number must be positive"
                                                else if Z.ltb 1114111 n || (Z.leb 55296 n && Z.leb n 57343)
                                                then Value_Err "requested character not valid for encoding"
                                                else Value_string (Some (txt (n :: nil)))
                                    | None => Value_string None end
                      | _ => Value_Err "wrong number of arguments" end)
  :: ("to_hex", fun l => match l with
                         | v :: nil => match int_parts v with
                                       | Some (z, w) => let b := if Nat.eqb w 64 then 64%nat else 32%nat in
                                                        let u := Z.modulo z (2 ^ Z.of_nat b) in
                                                        let h := hex_of_bytes false (bytes_be (Nat.div b 8) u) in
                                                        (* without the leading zeros *)
                                                        let fix strip (s : string) :=
                                                            match s with String "0"%char ((String _ _) as r) => strip r | _ => s end in
                                                        Value_string (Some (strip h))
                                       | None => Value_string None end
                         | _ => Value_Err "wrong number of arguments" end)
  :: ("octet_length", fun l => match texts k l with
                               | Some (s :: nil) => Value_I (Some (Z.of_nat (String.length s), 32%nat))
                               | _ => Value_I None end)
  :: ("num_nulls", fun l => VInt 32 (Z.of_nat (List.length (filter is_null l))))
  :: ("num_nonnulls", fun l => VInt 32 (Z.of_nat (List.length (filter (fun v => negb (is_null v)) l))))
  :: ("bit_length", fun l => match texts k l with
                             | Some (s :: nil) => Value_I (Some (8 * Z.of_nat (String.length s), 32%nat))
                             | _ => Value_I None end)
  :: nil.

(** ** Comparisons and conditionals (TODO 2.3): [BETWEEN SYMMETRIC] holds when [x] is between the two
    bounds in either order; [num_nulls] and [num_nonnulls] count the NULL arguments *)
Definition pg_between (l : list value) : bool3 :=
  match string_assoc _ "between" predicate_table with Some p => p l | None => unknown3 end.

Definition pg_extra_preds : list (string * (list value -> bool3)) :=
     ("between symmetric", fun l => match l with
                                    | x :: a :: b :: nil => orb3 (pg_between (x :: a :: b :: nil)) (pg_between (x :: b :: a :: nil))
                                    | _ => unknown3 end)
  :: ("not between symmetric", fun l => match l with
                                        | x :: a :: b :: nil => negb3 (orb3 (pg_between (x :: a :: b :: nil)) (pg_between (x :: b :: a :: nil)))
                                        | _ => unknown3 end)
  :: nil.

(** ** Regular expressions (TODO 2.4): Advanced Regular Expressions ([src/backend/regex]): the longest or the
    shortest match by the greediness of the expression; [.] matches a line break by default; the
    replacement refers to the groups by [\n] and to the match by [\&]; [regexp_replace] replaces the first
    match unless the flag [g] *)
Definition pg_rx : rx_env := mk_rx_env pg_skit fl_pg true false true false "invalid regular expression".

Definition pg_regex_preds : list (string * (list value -> bool3)) :=
     ("~", rx_like pg_rx false) :: ("~*", rx_like pg_rx true)
  :: ("!~", fun l => negb3 (rx_like pg_rx false l)) :: ("!~*", fun l => negb3 (rx_like pg_rx true l))
  :: ("similar to", pg_similar pg_rx) :: ("not similar to", fun l => negb3 (pg_similar pg_rx l))
  :: nil.

Definition pg_regex_funs : list (string * (list value -> value)) :=
     ("regexp_replace", pg_regexp_replace pg_rx)
  :: ("regexp_count", rx_count pg_rx)
  :: ("regexp_instr", rx_instr pg_rx)
  :: ("regexp_substr", rx_substr pg_rx)
  :: ("regexp_like", fun l => match rx_like pg_rx false l with
                              | true3 => Value_bool (Some true) | false3 => Value_bool (Some false)
                              | _ => match l with
                                     | s :: p :: rest => match rx_setup pg_rx s p (opt_val rest 0) with
                                                         | Some None => Value_Err "invalid regular expression"
                                                         | _ => Value_bool None end
                                     | _ => Value_bool None end end)
  :: ("substring_regex", pg_substring_regex pg_rx)
  :: nil.

(** ** Aggregates (TODO 2.5): the variance and the standard deviation are [numeric] (of integers and [numeric]
    values) or [double precision]; [variance] and [stddev] are the sample ones; the statistics of two
    variables are [double precision] *)
Definition pg_aggregates : list (string * (list value -> value)) :=
     ("var_pop", pg_var_agg false false) :: ("var_samp", pg_var_agg true false) :: ("variance", pg_var_agg true false)
  :: ("stddev_pop", pg_var_agg false true) :: ("stddev_samp", pg_var_agg true true) :: ("stddev", pg_var_agg true true)
  :: ("bit_xor", bit_xor_agg false is_null num_of_value)
  :: ("any_value", any_value_agg is_null)
  :: map (fun w => (w, stat2_agg w is_null num_of_value))
         ("covar_pop" :: "covar_samp" :: "corr" :: "regr_count" :: "regr_slope" :: "regr_intercept" :: "regr_r2"
          :: "regr_sxx" :: "regr_syy" :: "regr_sxy" :: "regr_avgx" :: "regr_avgy" :: nil)%string
  ++ ("json_agg", json_array_agg 1 pg_json_of_value) :: ("jsonb_agg", json_array_agg 0 pg_json_of_value)
  :: ("json_object_agg", json_object_agg 1 is_null text_of pg_json_of_value)
  :: ("jsonb_object_agg", json_object_agg 0 is_null text_of pg_json_of_value)
  :: ordered_set_table false is_null num_of_value sql_order.

(** ** Date and time functions (TODO 2.7) *)
Definition pg_time_funs : list (string * (list value -> value)) :=
     ("age", fun l => match l with
                      | a :: b :: nil => match to_ts a, to_ts b with Some x, Some y => pg_age x y | _, _ => Value_V None end
                      (* [age (t)]: from midnight of the current date *)
                      | a :: nil => match to_ts a with Some y => pg_age (ts_of (ts_days statement_time) 0) y | None => Value_V None end
                      | _ => Value_Err "function does not exist" end)
  :: ("to_date", fun l => match l with
                          | s :: f :: nil => match text_of s, text_of f with
                                             | Some s, Some f => match pg_to_timestamp s f with
                                                                 | Some t => VDate (ts_days t)
                                                                 | None => Value_Err "invalid value for to_date" end
                                             | _, _ => Value_T None end
                          | _ => Value_Err "function does not exist" end)
  :: ("to_timestamp", fun l => match l with
                               | s :: f :: nil => match text_of s, text_of f with
                                                  | Some s, Some f => match pg_to_timestamp s f with
                                                                      | Some t => VTsTz t 6
                                                                      | None => Value_Err "invalid value for to_timestamp" end
                                                  | _, _ => Value_T None end
                               (* [to_timestamp (epoch)] *)
                               | v :: nil => match num_of_value v with
                                             | Some n => VTsTz (ts_of (days_from_civil 1970 1 1) 0 + Qc_round (Qcmult (Qc_of_num n) (Qc_of_Z 1000000))) 6
                                             | None => Value_T None end
                               | _ => Value_Err "function does not exist" end)
  :: ("make_time", fun l => match l with
                            | h :: m :: sec :: nil => match int_parts h, int_parts m, num_of_value sec with
                                                      | Some (h, _), Some (m, _), Some se =>
                                                        let us := Qc_round (Qcmult (Qc_of_num se) (Qc_of_Z 1000000)) in
                                                        if (Z.ltb h 0) || (Z.ltb 23 h) || (Z.ltb m 0) || (Z.ltb 59 m) || (Z.ltb us 0) || (Z.leb 60000000 us)
                                                        then Value_Err "time field value out of range"
                                                        else VTime ((h * 60 + m) * 60000000 + us) 6
                                                      | _, _, _ => Value_T None end
                            | _ => Value_Err "function does not exist" end)
  :: ("make_timestamp", fun l => match l with
                                 | y :: mo :: d :: h :: mi :: sec :: nil =>
                                   match int_parts y, int_parts mo, int_parts d, int_parts h, int_parts mi, num_of_value sec with
                                   | Some (y, _), Some (mo, _), Some (d, _), Some (h, _), Some (mi, _), Some se =>
                                     let us := Qc_round (Qcmult (Qc_of_num se) (Qc_of_Z 1000000)) in
                                     if negb (valid_date y mo d) then Value_Err "date field value out of range"
                                     else if (Z.ltb h 0) || (Z.ltb 23 h) || (Z.ltb mi 0) || (Z.ltb 59 mi) || (Z.ltb us 0) || (Z.leb 60000000 us)
                                     then Value_Err "time field value out of range"
                                     else VTs (ts_of (days_from_civil y mo d) ((h * 60 + mi) * 60000000 + us)) 6
                                   | _, _, _, _, _, _ => Value_T None end
                                 | _ => Value_Err "function does not exist" end)
  (* [make_interval (years, months, weeks, days, hours, mins, secs)], missing arguments being 0 *)
  :: ("make_interval", fun l =>
        let z i := match nth_error l i with Some v => match int_parts v with Some (z, _) => z | None => 0 end | None => 0 end in
        let secs := match nth_error l 6 with Some v => match num_of_value v with Some n => Qc_round (Qcmult (Qc_of_num n) (Qc_of_Z 1000000)) | None => 0 end | None => 0 end in
        VIntv (z 0%nat * 12 + z 1%nat) (z 2%nat * 7 + z 3%nat) ((z 4%nat * 60 + z 5%nat) * 60000000 + secs))
  :: ("justify_days", fun l => match l with Value_V (Some (mo, d, us)) :: nil => let '(a, b, c) := justify_days mo d us in VIntv a b c | _ => Value_V None end)
  :: ("justify_hours", fun l => match l with Value_V (Some (mo, d, us)) :: nil => let '(a, b, c) := justify_hours mo d us in VIntv a b c | _ => Value_V None end)
  :: ("justify_interval", fun l => match l with
                                   | Value_V (Some (mo, d, us)) :: nil =>
                                     let '(mo, d, us) := justify_hours mo d us in let '(a, b, c) := justify_days mo d us in VIntv a b c
                                   | _ => Value_V None end)
  :: ("date_bin", fun l => match l with
                           | Value_V (Some (mo, d, us)) :: src :: org :: nil =>
                             if negb (Z.eqb mo 0) then Value_Err "timestamps cannot be binned into intervals containing months or years"
                             else match to_ts src, to_ts org with
                                  | Some x, Some o => match date_bin (d * 86400000000 + us) x o with
                                                      | Some r => VTs r 6 | None => Value_Err "stride must be greater than zero" end
                                  | _, _ => Value_T None end
                           | _ => Value_T None end)
  :: ("isfinite", fun l => match l with v :: nil => if is_null v then Value_bool None else Value_bool (Some true) | _ => Value_bool None end)
  :: ("clock_timestamp", fun _ => VTsTz statement_time 6) :: ("statement_timestamp", fun _ => VTsTz statement_time 6)
  :: ("transaction_timestamp", fun _ => VTsTz statement_time 6)
  :: nil.

(** ** Arrays (TODO 2.8): one-dimensional arrays, a [Value_J] of kind 2 (the JSON array of the elements);
    the indexes start at 1 *)
Definition is_J (v : value) : bool := match v with Value_J (Some (_, 2%nat)) => false | Value_J _ => true | _ => false end.
Definition is_A (v : value) : bool := match v with Value_J (Some (_, 2%nat)) => true | _ => false end.

Definition VArr (l : list value) : value := Value_J (Some (text_compact (JArr (map pg_json_of_value l)), 2%nat)).

Definition value_of_jelem (j : json) : value :=
  match j with
  | JNull => Value_Z None
  | JNum t => match json_num_qc t with
              | Some q => if existsb (Ascii.eqb "."%char) (list_ascii_of_string t)
                          then VDec q (qc_scale q) (qc_scale q)
                          else let z := Qc_round q in if int_range_ok 32 z then VInt 32 z else Value_Z (Some z)
              | None => Value_string (Some t) end
  | JStr t => Value_string (Some t)
  | JBool b => Value_bool (Some b)
  | _ => VJ 0 j
  end.

Definition arr_elems (v : value) : option (list value) :=
  match v with
  | Value_J (Some (t, 2%nat)) => match parse_json t with Some (JArr l) => Some (map value_of_jelem l) | _ => None end
  | _ => None
  end.

(** two elements are not distinct ([IS NOT DISTINCT FROM]) *)
Definition not_distinct (a b : value) : bool :=
  if is_null a then is_null b else if is_null b then false else match sql_compare a b with Some Eq => true | _ => false end.

Definition with_arr (null : value) (v : value) (f : list value -> value) : value :=
  match arr_elems v with Some l => f l | None => null end.

Definition pg_array_funs : list (string * (list value -> value)) :=
     ("array", fun l => VArr l)
  :: ("array_length", fun l => match l with
                               | a :: d :: nil => with_arr (Value_I None) a (fun xs => match int_parts d, xs with
                                                                                       | Some (1, _), _ :: _ => VInt 32 (Z.of_nat (List.length xs))
                                                                                       | _, _ => Value_I None end)
                               | _ => Value_Err "function does not exist" end)
  :: ("cardinality", fun l => match l with a :: nil => with_arr (Value_I None) a (fun xs => VInt 32 (Z.of_nat (List.length xs))) | _ => Value_Err "function does not exist" end)
  :: ("array_lower", fun l => match l with a :: _ :: nil => with_arr (Value_I None) a (fun xs => match xs with nil => Value_I None | _ => VInt 32 1 end) | _ => Value_I None end)
  :: ("array_upper", fun l => match l with a :: _ :: nil => with_arr (Value_I None) a (fun xs => match xs with nil => Value_I None | _ => VInt 32 (Z.of_nat (List.length xs)) end) | _ => Value_I None end)
  :: ("array_ndims", fun l => match l with a :: nil => with_arr (Value_I None) a (fun xs => match xs with nil => Value_I None | _ => VInt 32 1 end) | _ => Value_I None end)
  :: ("array_dims", fun l => match l with a :: nil => with_arr (Value_string None) a (fun xs => match xs with nil => Value_string None | _ => Value_string (Some ("[1:" ++ string_of_Z (Z.of_nat (List.length xs)) ++ "]")) end) | _ => Value_string None end)
  :: ("array_append", fun l => match l with a :: e :: nil => with_arr (Value_J None) a (fun xs => VArr (xs ++ e :: nil)) | _ => Value_Err "function does not exist" end)
  :: ("array_prepend", fun l => match l with e :: a :: nil => with_arr (Value_J None) a (fun xs => VArr (e :: xs)) | _ => Value_Err "function does not exist" end)
  :: ("array_cat", fun l => match l with a :: b :: nil => match arr_elems a, arr_elems b with
                                                           | Some x, Some y => VArr (x ++ y) | Some _, None => a | None, Some _ => b
                                                           | None, None => Value_J None end
                                         | _ => Value_Err "function does not exist" end)
  :: ("array_position", fun l => match l with
                                 | a :: e :: rest =>
                                   let start := match rest with s :: _ => match int_parts s with Some (z, _) => z | None => 1 end | nil => 1 end in
                                   with_arr (Value_I None) a (fun xs =>
                                     match find (fun p => Z.leb start (fst p) && not_distinct (snd p) e) (combine (map Z.of_nat (seq 1 (List.length xs))) xs) with
                                     | Some (i, _) => VInt 32 i | None => Value_I None end)
                                 | _ => Value_Err "function does not exist" end)
  :: ("array_positions", fun l => match l with
                                  | a :: e :: nil => with_arr (Value_J None) a (fun xs =>
                                      VArr (map (fun p => VInt 32 (fst p)) (filter (fun p => not_distinct (snd p) e) (combine (map Z.of_nat (seq 1 (List.length xs))) xs))))
                                  | _ => Value_Err "function does not exist" end)
  :: ("array_remove", fun l => match l with a :: e :: nil => with_arr (Value_J None) a (fun xs => VArr (filter (fun x => negb (not_distinct x e)) xs)) | _ => Value_Err "function does not exist" end)
  :: ("array_replace", fun l => match l with a :: e :: r :: nil => with_arr (Value_J None) a (fun xs => VArr (map (fun x => if not_distinct x e then r else x) xs)) | _ => Value_Err "function does not exist" end)
  :: ("array_to_string", fun l => match l with
                                  | a :: sep :: rest =>
                                    match text_of sep with
                                    | Some sp =>
                                      let nulls := match rest with n :: _ => text_of n | nil => None end in
                                      with_arr (Value_string None) a (fun xs =>
                                        Value_string (Some (String.concat sp (flat_map (fun x => if is_null x then match nulls with Some n => n :: nil | None => nil end
                                                                                                    else match text_of x with Some t => t :: nil | None => nil end) xs))))
                                    | None => Value_string None end
                                  | _ => Value_Err "function does not exist" end)
  :: ("string_to_array", fun l => match l with
                                  | s :: sep :: rest =>
                                    match text_of s with
                                    | Some t =>
                                      let nulls := match rest with n :: _ => text_of n | nil => None end in
                                      let parts := match sep with
                                                   | Value_string (Some EmptyString) => match t with EmptyString => nil | _ => t :: nil end
                                                   | _ => match text_of sep with
                                                          | Some d => match t with EmptyString => nil | _ => map txt (split_cp (cps d) (cps t)) end
                                                          | None => map (fun c => txt (c :: nil)) (cps t) end
                                                   end in
                                      VArr (map (fun p => match nulls with
                                                          | Some n => if String.eqb p n then Value_string None else Value_string (Some p)
                                                          | None => Value_string (Some p) end) parts)
                                    | None => Value_J None end
                                  | _ => Value_Err "function does not exist" end)
  :: ("subscript", fun l => match l with
                            | a :: i :: nil => with_arr (Value_Z None) a (fun xs => match int_parts i with
                                                                                   | Some (k, _) => if Z.leb 1 k then nth (Z.to_nat (k - 1)) xs (Value_Z None) else Value_Z None
                                                                                   | None => Value_Z None end)
                            | _ => Value_Err "function does not exist" end)
  :: ("slice", fun l => match l with
                        | a :: lo :: hi :: nil => with_arr (Value_J None) a (fun xs => match int_parts lo, int_parts hi with
                                                                                       | Some (x, _), Some (y, _) => let x := Z.max 1 x in
                                                                                         VArr (firstn (Z.to_nat (y - x + 1)) (skipn (Z.to_nat (x - 1)) xs))
                                                                                       | _, _ => Value_J None end)
                        | _ => Value_Err "function does not exist" end)
  :: nil.

(** [x op ANY (array)], [x op ALL (array)]; [@>], [<@], [&&] of arrays *)
Definition pg_quant_array (all : bool) (op : string) (l : list value) : bool3 :=
  match l with
  | x :: a :: nil =>
    match arr_elems a, string_assoc _ op predicate_table with
    | Some xs, Some p => let rs := map (fun e => p (x :: e :: nil)) xs in
                         if all then fold_left andb3 rs true3 else fold_left orb3 rs false3
    | _, _ => unknown3
    end
  | _ => unknown3
  end.

Definition pg_array_preds : list (string * (list value -> bool3)) :=
  flat_map (fun op => ((op ++ "any")%string, pg_quant_array false op) :: ((op ++ "all")%string, pg_quant_array true op) :: nil)
           ("=" :: "<>" :: "<" :: "<=" :: ">" :: ">=" :: nil)%string
  ++ ("&&", fun l => match l with
                     | a :: b :: nil => match arr_elems a, arr_elems b with
                                        | Some x, Some y => bool3_of_bool (existsb (fun e => negb (is_null e) && existsb (fun f => negb (is_null f) && not_distinct e f) y) x)
                                        | _, _ => unknown3 end
                     | _ => unknown3 end)
  :: ("@>", fun l => match l with
                     | a :: b :: nil => if is_A a then match arr_elems a, arr_elems b with
                                                       | Some x, Some y => bool3_of_bool (forallb (fun f => negb (is_null f) && existsb (fun e => negb (is_null e) && not_distinct e f) x) y)
                                                       | _, _ => unknown3 end
                                        else match string_assoc _ "@>" predicate_table with Some p => p l | None => unknown3 end
                     | _ => unknown3 end)
  :: ("<@", fun l => match l with
                     | a :: b :: nil => if is_A a then match arr_elems a, arr_elems b with
                                                       | Some x, Some y => bool3_of_bool (forallb (fun f => negb (is_null f) && existsb (fun e => negb (is_null e) && not_distinct e f) y) x)
                                                       | _, _ => unknown3 end
                                        else match string_assoc _ "<@" predicate_table with Some p => p l | None => unknown3 end
                     | _ => unknown3 end)
  :: nil.

(** ** [jsonb] functions and operators (TODO 2.8): [jsonb_set], [jsonb_insert], [jsonb_strip_nulls],
    [jsonb_pretty], [#-], [||] and [-] on [jsonb]; the paths are text arrays ['{a,0}'] *)
Definition pg_old (name : string) : list value -> value :=
  match string_assoc _ name symbol_table with Some g => g | None => fun _ => Value_Z None end.


Definition pg_json_funs : list (string * (list value -> value)) :=
     ("jsonb_set", fun l => match l with
                            | t :: p :: v :: rest =>
                              let create := match rest with Value_bool (Some false) :: _ => false | _ => true end in
                              match json_of_J t, text_of p, json_of_J v with
                              | Some j, Some ps, Some nv => match pg_text_array ps with
                                                            | Some path => VJ 0 (pg_set create path j nv)
                                                            | None => Value_Err "malformed array literal" end
                              | _, _, _ => Value_J None end
                            | _ => Value_Err "function does not exist" end)
  :: ("jsonb_insert", fun l => match l with
                               | t :: p :: v :: rest =>
                                 let after := match rest with Value_bool (Some true) :: _ => true | _ => false end in
                                 match json_of_J t, text_of p, json_of_J v with
                                 | Some j, Some ps, Some nv => match pg_text_array ps with
                                                               | Some path => VJ 0 (pg_insert after path j nv)
                                                               | None => Value_Err "malformed array literal" end
                                 | _, _, _ => Value_J None end
                               | _ => Value_Err "function does not exist" end)
  :: ("jsonb_strip_nulls", fun l => match l with v :: nil => match json_of_J v with Some j => VJ 0 (strip_nulls j) | None => Value_J None end | _ => Value_J None end)
  :: ("json_strip_nulls", fun l => match l with v :: nil => match json_of_J v with Some j => VJ 1 (strip_nulls j) | None => Value_J None end | _ => Value_J None end)
  :: ("jsonb_pretty", fun l => match l with v :: nil => match json_of_J v with Some j => Value_string (Some (pretty 4 j)) | None => Value_string None end | _ => Value_string None end)
  :: ("#-", fun l => match l with
                     | t :: p :: nil => match json_of_J t, text_of p with
                                        | Some j, Some ps => match pg_text_array ps with
                                                             | Some path => VJ 0 (pg_remove path j)
                                                             | None => Value_Err "malformed array literal" end
                                        | _, _ => Value_J None end
                     | _ => Value_Err "operator does not exist" end)
  :: ("||", fun l => match l with
                     | a :: b :: nil => if is_A a || is_A b
                                        then match arr_elems a, arr_elems b with
                                             | Some x, Some y => VArr (x ++ y)
                                             | Some x, None => VArr (x ++ b :: nil)
                                             | None, Some y => VArr (a :: y)
                                             | None, None => Value_J None end
                                        else if is_J a && is_J b
                                        then match json_of_J a, json_of_J b with Some x, Some y => VJ 0 (pg_concat x y) | _, _ => Value_J None end
                                        else pg_old "||" l
                     | _ => pg_old "||" l end)
  :: ("-", fun l => match l with
                    | a :: b :: nil => if is_J a
                                       then match json_of_J a, b with
                                            | Some x, (Value_string (Some k) | Value_C (Some (k, _))) => VJ 0 (pg_minus_key x k)
                                            | Some x, _ => match int_parts b with Some (i, _) => VJ 0 (pg_minus_idx x i) | None => Value_J None end
                                            | None, _ => Value_J None end
                                       else pg_old "-" l
                    | _ => pg_old "-" l end)
  :: nil.

(** [?|] and [?&]: any or all of the keys of a text array *)
Definition pg_json_preds : list (string * (list value -> bool3)) :=
     ("?|", fun l => match l with
                     | a :: k :: nil => match json_of_J a, text_of k with
                                        | Some (JObj ms), Some ks => match pg_text_array ks with
                                                                     | Some keys => bool3_of_bool (existsb (fun x => existsb (fun m => String.eqb (fst m) x) ms) keys)
                                                                     | None => unknown3 end
                                        | Some _, Some _ => false3
                                        | _, _ => unknown3 end
                     | _ => unknown3 end)
  :: ("?&", fun l => match l with
                     | a :: k :: nil => match json_of_J a, text_of k with
                                        | Some (JObj ms), Some ks => match pg_text_array ks with
                                                                     | Some keys => bool3_of_bool (forallb (fun x => existsb (fun m => String.eqb (fst m) x) ms) keys)
                                                                     | None => unknown3 end
                                        | Some _, Some _ => false3
                                        | _, _ => unknown3 end
                     | _ => unknown3 end)
  :: nil.

(** [substr] is a synonym of [substring] *)
Definition pg_symbol_table : list (string * (list value -> value)) :=
  sys_table default_env "PostgreSQL" ++ pg_array_funs ++ pg_json_funs ++ pg_time_funs ++ pg_regex_funs ++ pg_string_table ++
  match string_assoc _ "substring" symbol_table with
  | Some f => ("substr", f) :: symbol_table
  | None => symbol_table
  end.

Definition PostgreSQL : vsem :=
  mk_vsem "PostgreSQL"
          (table_of_list (like_table pg_skit false (fun c => c) low_cp (Some 92) ++ pg_regex_preds ++ pg_array_preds ++ pg_json_preds ++ pg_extra_preds ++ predicate_table))
          (table_of_list pg_symbol_table)
          (table_of_list (("array_agg", fun l => VArr l) :: pg_aggregates ++ filter (fun p => negb (String.eqb (fst p) "group_concat")) aggregate_table
                          ++ ("string_agg_sep", agg_concat_sep_by is_null "") :: nil))
          is_null
          (fun v => match v with
                    | Value_string (Some s) => match bool_of_string s with Some b => bool3_of_bool b | None => unknown3 end
                    | _ => bool3_of_value v end)
          value_of_bool3
          sql_eq3
          sql_order
          canon_numeric
          false
          (fun f => match f with F_Bare_Column | F_Fetch_Percent | F_Null_Treatment | F_From_Last => false | _ => true end)
          false
          (* an escape of more than one character: [invalid escape string] *)
          (fun p l => bad_escape pg_skit p l || rx_bad pg_rx ("~" :: "~*" :: "!~" :: "!~*" :: nil)%string p l)
          (* an integer literal is an [integer] if it fits, a [bigint] if it fits, a [numeric] otherwise
             ([make_const] in [src/backend/parser/parse_node.c]) *)
          (fun v => match v with
                    | Value_Z (Some z) => if int_range_ok 32 z then VInt 32 z 
                                          else if int_range_ok 64 z then v else VDec (Qc_of_Z z) 0 0
                    | _ => v end)
          (* a condition must be a boolean ([coerce_to_boolean]): a string is read as a boolean literal
             (['true'], ['t'], ['yes'], ['1'], ...), another value is a type error *)
          (fun v => if is_null v then false
                    else match v with
                         | Value_bool _ => false
                         | Value_string (Some s) => match bool_of_string s with Some _ => false | None => true end
                         | _ => true end)
          (fun _ _ l => l).
