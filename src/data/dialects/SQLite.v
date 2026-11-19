(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**                            The SQLite dialect                                   *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String Ascii ZArith NArith QArith Qcanon.

Require Import Bool3 OrderedSet SqlFull Values Dialects ValueKit PostgreSQL MySQL.

Close Scope Q_scope.
Close Scope Qc_scope.
Open Scope string_scope.
Open Scope Z_scope.

Import NullValues.

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

Definition lite_compare (v1 v2 : value) : option comparison :=
  if (is_null v1 || is_null v2)%bool then None
  else match v1, v2 with
       | Value_string (Some a), Value_string (Some b) => Some (string_compare a b)
       | Value_string _, _ => Some Gt
       | _, Value_string _ => Some Lt
       | _, _ => match lenient v1, lenient v2 with
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
  | Value_Q (Some _) => "real"
  | Value_string (Some _) => "text"
  | _ => "null"
  end.

Definition lite_concat (l : list value) : value :=
  if existsb is_null l then Value_string None
  else Value_string (Some (fold_left (fun acc v => match text_of v with Some s => acc ++ s | None => acc end) l EmptyString)).

(** [concat] and [concat_ws] ignore the NULLs *)
Definition lite_concat_skip (l : list value) : value :=
  Value_string (Some (fold_left (fun acc v => match text_of v with Some s => acc ++ s | None => acc end) l EmptyString)).

Definition lite_symbol_table : list (string * (list value -> value)) :=
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
  :: ("typeof", fun l => match l with v :: nil => Value_string (Some (type_name v)) | _ => Value_string None end)
  (* logic *)
  :: ("and", logic_and) :: ("or", logic_or)
  :: ("not", fun l => match l with v :: nil => lite_of_truth (negb3 (lite_truth v)) | _ => Value_Z None end)
  (* strings *)
  :: ("||", lite_concat)
  :: ("concat", lite_concat_skip)
  :: ("length", str1 (fun s => Value_Z (Some (Z.of_nat (String.length s)))))
  :: ("upper", str_fun1 upper_s) :: ("lower", str_fun1 lower_s)
  :: ("trim", str_fun1 (fun s => string_rtrim (string_ltrim s)))
  :: ("ltrim", str_fun1 string_ltrim) :: ("rtrim", str_fun1 string_rtrim)
  :: ("substr", lite_substr_fun) :: ("substring", lite_substr_fun)
  :: ("replace", fun l => match l with
                          | s :: f :: t :: nil => match text_of s, text_of f, text_of t with
                                                  | Some s, Some f, Some t => Value_string (Some (string_replace s f t))
                                                  | _, _, _ => Value_string None end
                          | _ => Value_string None end)
  :: ("instr", fun l => match l with
                        | s :: sub :: nil => match text_of s, text_of sub with
                                             | Some s, Some sub => Value_Z (Some (string_index sub s))
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

Definition lite_aggregate_table : list (string * (list value -> value)) :=
     ("count", agg_count_by is_null)
  :: ("count(*)", fun l => Value_Z (Some (Z.of_nat (List.length l))))
  :: ("sum", agg_sum_by is_null lenient)
  :: ("total", fun l => match agg_sum_by is_null lenient l with
                        | Value_Z None => Value_Q (Some (Qc_of_Z 0))
                        | v => match lenient v with Some n => Value_Q (Some (Qc_of_num n)) | None => v end
                        end)
  :: ("avg", agg_avg_by is_null lenient)
  :: ("min", agg_extremum_by is_null lite_order is_Lt)
  :: ("max", agg_extremum_by is_null lite_order is_Gt)
  :: ("group_concat", agg_concat_by is_null ",")
  :: nil.

(** The constructs of SQLite 3.39 and later: no [LATERAL], no [INTERSECT ALL] nor 
    [EXCEPT ALL], no [ANY] and [ALL] subqueries. *)
Definition lite_supports (f : feature) : bool :=
  match f with
  | F_Lateral | F_Intersect_All | F_Except_All | F_Any_All 
  | F_Grouping_Sets | F_Rollup | F_Cube => false
  | _ => true
  end.

Definition canon_lite (v : value) : value :=
  match v with
  | Value_bool (Some b) => Value_Q (Some (Qc_of_Z (if b then 1 else 0)))
  | _ => canon_numeric v
  end.

Definition SQLite : vsem :=
  mk_vsem "SQLite"
          (table_of_list lite_pred_table)
          (table_of_list lite_symbol_table)
          (table_of_list lite_aggregate_table)
          is_null
          lite_truth
          lite_of_truth
          lite_eq3
          lite_order
          canon_lite
          true
          lite_supports.
