(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**                            The MySQL dialect                                    *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String Ascii ZArith NArith QArith Qcanon.

Require Import Bool3 OrderedSet SqlFull Values Dialects ValueKit PostgreSQL.

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
Section Collation.

Variable pad : bool.

(** is the collation case insensitive? (false for a binary collation, as TiDB's default [utf8mb4_bin]) *)
Variable ci : bool.

(** The key of a string for a comparison *)
Definition coll_key (s : string) : string := (if ci then lower_s else fun x => x) (if pad then string_rtrim s else s).

(** the system variable [div_precision_increment], whose default value is 4 in MySQL and in OceanBase *)
Definition div_precision_increment : nat := 4%nat.

Definition my_isnull := is_null.

Definition my_compare (v1 v2 : value) : option comparison :=
  if (is_null v1 || is_null v2)%bool then None
  else match v1, v2 with
       | Value_string (Some a), Value_string (Some b) => Some (string_compare (coll_key a) (coll_key b))
       | _, _ => match lenient v1, lenient v2 with
                 | Some a, Some b => Some (num_cmp a b)
                 | _, _ => None
                 end
       end.

Definition my_order (a b : value) : comparison :=
  match my_compare a b with Some c => c | None => value_compare a b end.

Definition my_truth (v : value) : bool3 :=
  match lenient v with 
  | Some n => bool3_of_bool (negb (num_is_zero n)) 
  | None => unknown3 
  end.

Definition my_of_truth (b : bool3) : value :=
  match b with true3 => Value_Z (Some 1) | false3 => Value_Z (Some 0) | unknown3 => Value_Z None end.

Definition my_eq3 (a b : value) : bool3 := cmp_pred my_compare is_Eq (a :: b :: nil).

(** [x <=> y]: equality which is never UNKNOWN. *)
Definition my_null_safe_eq (a b : value) : bool3 :=
  match is_null a, is_null b with
  | true, true => true3
  | false, false => my_eq3 a b
  | _, _ => false3
  end.

Definition truth_is (t : bool3) (v : value) : bool3 :=
  bool3_of_bool (match my_truth v, t with
                 | true3, true3 | false3, false3 | unknown3, unknown3 => true
                 | _, _ => false
                 end).

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
                                  | Some s, Some p => bool3_of_bool (like_gen (Some "\"%char) (lower_s p) (lower_s s))
                                  | _, _ => unknown3 end))
  :: ("not like", binary3 (fun v p => negb3 (match text_of v, text_of p with
                                  | Some s, Some p => bool3_of_bool (like_gen (Some "\"%char) (lower_s p) (lower_s s))
                                  | _, _ => unknown3 end)))
  :: ("true", fun _ => true3)
  :: ("false", fun _ => false3)
  :: ("unknown", fun _ => unknown3)
  :: nil.

Definition str1 (f : string -> value) (l : list value) : value :=
  match l with
  | v :: nil => match text_of v with Some s => f s | None => Value_string None end
  | _ => Value_string None
  end.

Definition str_fun1 (f : string -> string) := str1 (fun s => Value_string (Some (f s))).

Definition z_arg (v : value) : option Z :=
  match lenient v with
  | Some (Num_Z z) => Some z
  | Some (Num_Q q) => Some (Qc_round q)
  | None => None
  end.

(** [CASE WHEN c1 THEN v1 ... ELSE e END] for a dialect where a value is a condition
    through [truth]. *)
Fixpoint case_gen (truth : value -> bool3) (d : value) (l : list value) : value :=
  match l with
  | nil => d
  | e :: nil => e
  | c :: v :: l => match truth c with true3 => v | _ => case_gen truth d l end
  end.

Definition case_by truth (l : list value) :=
  match l with
  | _ :: v :: _ => case_gen truth (default_value (type_of_value v)) l
  | _ => case_gen truth (Value_Z None) l
  end.

(** NULL as soon as one argument is NULL, else the extremum for [order]. *)
Definition extremum_strict (isnull : value -> bool) (order : value -> value -> comparison) 
           (keep : comparison -> bool) (l : list value) :=
  match l with
  | nil => Value_Z None
  | v :: rest => 
    if existsb isnull l then default_value (type_of_value v)
    else fold_left (fun a b => if keep (order a b) then a else b) rest v
  end.

Definition fold_truth (truth : value -> bool3) (op : bool3 -> bool3 -> bool3) (z : bool3) 
           (l : list value) : bool3 :=
  fold_left (fun acc v => op acc (truth v)) l z.

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
    | Some sub, Some s => Value_Z (Some (string_index (lower_s sub) (lower_s s)))
    | _, _ => Value_Z None
    end
  | sub :: s :: pos :: nil => 
    match text_of sub, text_of s with
    | Some sub, Some s => 
      let p := match z_arg pos with Some p => p | None => 0 end in
      let n := Z.of_nat (String.length s) in
      if Z.ltb p 1 || Z.ltb (n + 1) p 
      then Value_Z (Some 0)
      else let rest := String.substring (Z.to_nat (p - 1)) (String.length s) s in
           match string_index (lower_s sub) (lower_s rest) with
           | 0 => Value_Z (Some 0)
           | i => Value_Z (Some (i + p - 1))
           end
    | _, _ => Value_Z None
    end
  | _ => Value_Z None
  end.

Definition my_symbol_table : list (string * (list value -> value)) :=
  let conv := lenient in
  let plus := num_fun2 conv (fun a b => Some (num_plus a b)) in
  let minus := num_fun2 conv (fun a b => Some (num_minus a b)) in
  let mult := num_fun2 conv (fun a b => Some (num_mult a b)) in
  let opp := num_fun1 conv num_opp in
  let div := num_fun2 conv (num_div_dec div_precision_increment) in
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
  :: ("abs", num_fun1 conv num_abs)
  :: ("sign", num_fun1 conv num_sign)
  :: ("floor", num_fun1 conv num_floor)
  :: ("ceil", num_fun1 conv num_ceil) :: ("ceiling", num_fun1 conv num_ceil)
  :: ("round", fun l => match l with
                        | v :: nil => num_fun1 conv (fun a => num_round a 0) l
                        | v :: d :: nil => match conv v, z_arg d with
                                           | Some a, Some d => value_of_num (num_round a d) 
                                           | _, _ => Value_Z None end
                        | _ => Value_Z None end)
  :: ("truncate", fun l => match l with
                           | v :: d :: nil => match conv v, z_arg d with
                                              | Some a, Some d => value_of_num (num_trunc a d) 
                                              | _, _ => Value_Z None end
                           | _ => Value_Z None end)
  :: ("power", num_fun2 conv num_power) :: ("pow", num_fun2 conv num_power)
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
  :: ("or", logic_or) :: ("||", logic_or)
  :: ("xor", fun l => my_of_truth (fold_truth my_truth xor3 false3 l))
  :: ("not", fun l => match l with v :: nil => my_of_truth (negb3 (my_truth v)) | _ => Value_Z None end)
  (* strings *)
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
                                             | Some sub, Some s => Value_Z (Some (string_index (lower_s sub) (lower_s s)))
                                             | _, _ => Value_Z None end
                        | _ => Value_Z None end)
  (* casts *)
  :: ("cast_int", fun l => match l with v :: nil => Value_Z (z_arg v) | _ => Value_Z None end)
  :: ("cast_numeric", fun l => match l with
                               | v :: nil => match lenient v with Some n => Value_Q (Some (Qc_of_num n)) | None => Value_Q None end
                               | _ => Value_Q None end)
  :: ("cast_string", fun l => match l with v :: nil => Value_string (text_of v) | _ => Value_string None end)
  :: nil.

Definition my_aggregate_table : list (string * (list value -> value)) :=
     ("count", agg_count_by is_null)
  :: ("count(*)", fun l => Value_Z (Some (Z.of_nat (List.length l))))
  :: ("sum", agg_sum_by is_null lenient)
  :: ("avg", agg_avg_dec div_precision_increment is_null lenient)
  :: ("min", agg_extremum_by is_null my_order is_Lt)
  :: ("max", agg_extremum_by is_null my_order is_Gt)
  :: ("group_concat", agg_concat_by is_null ",")
  :: ("bit_and", agg_bit_by is_null Z.land)
  :: ("bit_or", agg_bit_by is_null Z.lor)
  :: ("var_pop", agg_var_by is_null lenient false)
  :: ("variance", agg_var_by is_null lenient false)
  :: ("var_samp", agg_var_by is_null lenient true)
  :: nil.

(** The constructs of MySQL 8.0 (8.0.31 and later for [INTERSECT] and [EXCEPT]). *)
Definition my_supports (f : feature) : bool :=
  match f with
  | F_Full_Join | F_Frame_Groups | F_Filter_Agg | F_Nulls_Order => false
  (* [ONLY_FULL_GROUP_BY] is in the default [sql_mode]; functional dependencies are not modelled *)
  | F_Bare_Column | F_Fetch_Ties | F_Fetch_Percent => false
  (* only [WITH ROLLUP] *)
  | F_Grouping_Sets | F_Cube => false
  | _ => true
  end.

Definition canon_my (v : value) : value :=
  match v with
  | Value_string (Some s) => Value_string (Some (coll_key s))
  | Value_bool (Some b) => Value_Q (Some (Qc_of_Z (if b then 1 else 0)))
  | _ => canon_numeric v
  end.

Definition mysql_vs (name : string) (supports : feature -> bool) : vsem :=
  mk_vsem name
          (table_of_list my_pred_table)
          (table_of_list my_symbol_table)
          (table_of_list my_aggregate_table)
          is_null
          my_truth
          my_of_truth
          my_eq3
          my_order
          canon_my
          true
          supports.

End Collation.

(** MySQL 8 with its default collation [utf8mb4_0900_ai_ci] (no padding). *)
Definition MySQL : vsem := mysql_vs false true "MySQL" my_supports.
