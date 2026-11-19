(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**                   The OceanBase dialects (MySQL and Oracle modes)               *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String Ascii ZArith NArith QArith Qcanon.

Require Import Bool3 OrderedSet SqlFull Values Dialects ValueKit PostgreSQL MySQL.

Close Scope Q_scope.
Close Scope Qc_scope.
Open Scope string_scope.
Open Scope Z_scope.

Import NullValues.

(** OceanBase has two compatibility modes, chosen when a tenant is created and which
    cannot be changed afterwards. *)

(** * MySQL mode

    The semantics of the values is that of MySQL. The constructs are those listed in the
    documentation of OceanBase 4.x: [FULL JOIN] is an extension of OceanBase, and
    [INTERSECT]/[EXCEPT] exist. The documentation does not say whether [INTERSECT ALL],
    [EXCEPT ALL] and [LATERAL] exist; they are taken as not supported, which is to be
    verified against a tenant. *)

Definition ob_my_supports (f : feature) : bool :=
  match f with
  | F_Frame_Groups | F_Filter_Agg | F_Nulls_Order | F_Lateral | F_Intersect_All | F_Except_All => false
  | _ => true
  end.

Definition OceanBaseMySQL : vsem :=
  mk_vsem "OceanBase (MySQL mode)"
          (vs_pred MySQL) (vs_symb MySQL) (vs_agg MySQL)
          (vs_is_null MySQL) (vs_truth MySQL) (vs_of_truth MySQL) (vs_eq3 MySQL)
          (vs_order MySQL) (vs_canon MySQL) (vs_nulls_smallest MySQL)
          ob_my_supports.

(** * Oracle mode

    - the empty string is NULL: a string function whose result is empty returns NULL, 
      [length('')] is NULL, and ['' = ''] is UNKNOWN;
    - there is no boolean type: a condition is not a value;
    - strings are compared byte by byte; a string compared with a number is converted to
      a number, and the comparison is UNKNOWN when it is not one (Oracle signals an
      error);
    - NULLs are the largest values of [ORDER BY]; [NULLS FIRST/LAST] is available
      (assumed from Oracle, to be verified);
    - [/] is the exact division, a division by zero is NULL (Oracle signals an error);
      [MOD(x, 0)] is [x];
    - [||] and [CONCAT] treat a NULL operand as the empty string: [NULL || 'a'] is ['a'];
    - [GREATEST] and [LEAST] are NULL as soon as one argument is NULL;
    - [SUBSTR] with a start of 0 starts at 1, and returns NULL for a length below 1;
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

Definition ora_str_fun1 (f : string -> string) := ora_str1 (fun s => Value_string (Some (f s))).

(** [NULL || x] is [x]; the result is NULL when both are. *)
Definition ora_concat (l : list value) : value :=
  if forallb ora_isnull l then Value_string None
  else Value_string (Some (fold_left (fun acc v => if ora_isnull v then acc 
                                                   else match text_of v with Some s => acc ++ s | None => acc end) 
                                     l EmptyString)).

Definition ora_substr (l : list value) : value :=
  match l with
  | s :: p :: rest =>
    if ora_isnull s then Value_string None
    else match text_of s, z_arg p, rest with
         | Some s, Some p, nil => 
           let p' := if Z.eqb p 0 then 1 else if Z.ltb p 0 then (Z.of_nat (String.length s) + p + 1) else p in
           Value_string (Some (sql_substring s p' None))
         | Some s, Some p, n :: nil =>
           match z_arg n with
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

Definition ora_symbol_table : list (string * (list value -> value)) :=
  let conv := strict_conv in
  let plus := num_fun2 conv (fun a b => Some (num_plus a b)) in
  let minus := num_fun2 conv (fun a b => Some (num_minus a b)) in
  let mult := num_fun2 conv (fun a b => Some (num_mult a b)) in
  let opp := num_fun1 conv num_opp in
  let div := num_fun2 conv num_div_exact in
     ("plus", plus) :: ("+", plus)
  :: ("minus", minus) :: ("-", minus)
  :: ("mult", mult) :: ("*", mult)
  :: ("opp", opp) :: ("neg", opp)
  :: ("/", div)
  :: ("mod", num_fun2 conv ora_mod)
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
  :: ("||", ora_concat) :: ("concat", ora_concat)
  :: ("length", ora_str1 (fun s => Value_Z (Some (Z.of_nat (String.length s)))))
  :: ("upper", ora_str_fun1 upper_s) :: ("lower", ora_str_fun1 lower_s)
  :: ("trim", ora_str_fun1 (fun s => string_rtrim (string_ltrim s)))
  :: ("ltrim", ora_str_fun1 string_ltrim) :: ("rtrim", ora_str_fun1 string_rtrim)
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
  :: ("variance", agg_var_by ora_isnull strict_conv true)
  :: ("var_samp", agg_var_by ora_isnull strict_conv true)
  :: ("var_pop", agg_var_by ora_isnull strict_conv false)
  :: nil.

(** The constructs of OceanBase in Oracle mode, from its documentation: [UNION [ALL]],
    [INTERSECT] and [MINUS]; the other ones are assumed from Oracle. [LATERAL] and the
    [ALL] forms of [INTERSECT] and [MINUS] are not supported. *)
Definition ora_supports (f : feature) : bool :=
  match f with
  | F_Lateral | F_Intersect_All | F_Except_All | F_Frame_Groups | F_Filter_Agg 
  | F_Cond_Value => false
  | _ => true
  end.

Definition canon_ora (v : value) : value :=
  if ora_isnull v then Value_Z None else canon_numeric v.

Definition OceanBaseOracle : vsem :=
  mk_vsem "OceanBase (Oracle mode)"
          (table_of_list ora_pred_table)
          (table_of_list ora_symbol_table)
          (table_of_list ora_aggregate_table)
          ora_isnull
          ora_truth
          (fun b => match b with true3 => Value_Z (Some 1) | false3 => Value_Z (Some 0) | unknown3 => Value_Z None end)
          ora_eq3
          ora_order
          canon_ora
          false
          ora_supports.
