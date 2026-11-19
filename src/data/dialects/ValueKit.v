(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**                 Building blocks for the value semantics of dialects             *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String Ascii ZArith NArith QArith Qcanon Qround.

Require Import Bool3 OrderedSet IEEE Values.

Close Scope Q_scope.
Close Scope Qc_scope.
Open Scope string_scope.

Import NullValues.

Open Scope Z_scope.

(** * Lenient conversion of strings to numbers

    MySQL and SQLite convert a string which is used as a number by reading its longest
    numeric prefix, and use 0 when there is none (['12abc'] is 12, ['abc'] is 0).
    Exponents are not read. *)

Fixpoint digits_aux (s : string) (acc : Z) (n : nat) : Z * nat * string :=
  match s with
  | String c r =>
    let d := (Z.of_nat (nat_of_ascii c) - 48)%Z in
    if ((0 <=? d)%Z && (d <=? 9)%Z)%bool then digits_aux r (acc * 10 + d)%Z (S n) else (acc, n, s)
  | EmptyString => (acc, n, s)
  end.

(** The number which is read, and whether the whole string (up to trailing blanks) has
    been read as a number. *)
Definition parse_number (s : string) : num * bool :=
  let s := string_ltrim s in
  let (neg, s) := match s with
                  | String "-" r => (true, r)
                  | String "+" r => (false, r)
                  | _ => (false, s)
                  end in
  let '(iv, ni, r) := digits_aux s 0%Z 0%nat in
  let '(fv, nf, r') := match r with
                       | String "." r2 => digits_aux r2 0%Z 0%nat
                       | _ => (0%Z, 0%nat, r)
                       end in
  let sgn z := if neg then Z.opp z else z in
  let n := if Nat.eqb nf 0%nat 
           then Num_Z (sgn iv)
           else Num_Q (Q2Qc (Qmake (sgn (iv * Z.pow 10 (Z.of_nat nf) + fv)) 
                                   (Z.to_pos (Z.pow 10 (Z.of_nat nf))))) in
  (n, if Nat.eqb (ni + nf)%nat 0%nat then false else if String.eqb (string_rtrim r') EmptyString then true else false).

Definition parse_prefix s : num := fst (parse_number s).

(** Numbers, with booleans as 0 and 1, and strings read leniently. *)
Definition lenient (v : value) : option num :=
  match v with
  | Value_Z (Some z) => Some (Num_Z z)
  | Value_Q (Some q) => Some (Num_Q q)
  | Value_D (Some (q, _, _)) => Some (Num_Q q)
  | Value_F (Some (q, k)) => if Nat.leb (Nat.div k 2) 1 then Some (Num_Q q) else None
  | Value_I (Some (z, _)) => Some (Num_Z z)
  | Value_bool (Some b) => Some (Num_Z (if b then 1%Z else 0%Z))
  | Value_string (Some s) => Some (parse_prefix s)
  | _ => None
  end.

(** Numbers, with strings which are numbers only; [None] for the other ones: this is the
    conversion of the dialects which signal an error otherwise. *)
Definition strict_conv (v : value) : option num :=
  match v with
  | Value_Z (Some z) => Some (Num_Z z)
  | Value_Q (Some q) => Some (Num_Q q)
  | Value_D (Some (q, _, _)) => Some (Num_Q q)
  | Value_F (Some (q, k)) => if Nat.leb (Nat.div k 2) 1 then Some (Num_Q q) else None
  | Value_I (Some (z, _)) => Some (Num_Z z)
  | Value_string (Some s) => 
    let (n, ok) := parse_number s in if ok then Some n else None
  | _ => None
  end.

(** * Operations on numbers *)

Definition num_cmp (a b : num) : comparison :=
  match a, b with
  | Num_Z x, Num_Z y => Z.compare x y
  | _, _ => Qccompare (Qc_of_num a) (Qc_of_num b)
  end.

Definition num_is_zero (a : num) := match num_cmp a (Num_Z 0) with Eq => true | _ => false end.

Definition num_plus a b := 
  match a, b with Num_Z x, Num_Z y => Num_Z (x + y) | _, _ => Num_Q (Qcplus (Qc_of_num a) (Qc_of_num b)) end.
Definition num_minus a b := 
  match a, b with Num_Z x, Num_Z y => Num_Z (x - y) | _, _ => Num_Q (Qcminus (Qc_of_num a) (Qc_of_num b)) end.
Definition num_mult a b := 
  match a, b with Num_Z x, Num_Z y => Num_Z (x * y) | _, _ => Num_Q (Qcmult (Qc_of_num a) (Qc_of_num b)) end.
Definition num_opp a := match a with Num_Z x => Num_Z (- x) | Num_Q q => Num_Q (Qcopp q) end.

(** exact division *)
Definition num_div_exact a b : option num := 
  if num_is_zero b then None else Some (Num_Q (Qcdiv (Qc_of_num a) (Qc_of_num b))).

(** integer part of the quotient, towards zero *)
Definition Qc_quot (a b : Qc) : Z := Qc_trunc (Qcdiv a b).

Definition num_div_trunc a b : option num :=
  if num_is_zero b then None 
  else match a, b with
       | Num_Z x, Num_Z y => Some (Num_Z (Z.quot x y))
       | _, _ => Some (Num_Z (Qc_quot (Qc_of_num a) (Qc_of_num b)))
       end.

(** remainder, with the sign of the dividend *)
Definition num_rem a b : option num :=
  if num_is_zero b then None 
  else match a, b with
       | Num_Z x, Num_Z y => Some (Num_Z (Z.rem x y))
       | _, _ => 
         let qa := Qc_of_num a in let qb := Qc_of_num b in
         Some (Num_Q (Qcminus qa (Qcmult qb (Qc_of_Z (Qc_quot qa qb)))))
       end.

Definition num_abs a := match num_cmp a (Num_Z 0) with Lt => num_opp a | _ => a end.
Definition num_sign a := Num_Z (match num_cmp a (Num_Z 0) with Lt => (-1)%Z | Eq => 0%Z | Gt => 1%Z end).

(** rounding to [d] decimals, ties away from zero *)
Definition num_round (a : num) (d : Z) : num :=
  match a with
  | Num_Z z => 
    if (0 <=? d)%Z then a 
    else let m := Z.pow 10 (Z.opp d) in
         let r := Z.quot (Z.abs z + m / 2) m * m in
         Num_Z (if (z <? 0)%Z then Z.opp r else r)
  | Num_Q q =>
    let scale := Qc_of_Z (Z.pow 10 (Z.abs d)) in
    let scaled := if (0 <=? d)%Z then Qcmult q scale else Qcdiv q scale in
    let r := Qc_round scaled in
    if (0 <=? d)%Z 
    then (if (d =? 0)%Z then Num_Z r else Num_Q (Qcdiv (Qc_of_Z r) scale))
    else Num_Z (r * Z.pow 10 (Z.opp d))
  end.

(** truncation to [d] decimals *)
Definition num_trunc (a : num) (d : Z) : num :=
  match a with
  | Num_Z z => 
    if (0 <=? d)%Z then a 
    else let m := Z.pow 10 (Z.opp d) in Num_Z (Z.quot z m * m)
  | Num_Q q =>
    let scale := Qc_of_Z (Z.pow 10 (Z.abs d)) in
    if (0 <=? d)%Z 
    then (if (d =? 0)%Z then Num_Z (Qc_trunc q) else Num_Q (Qcdiv (Qc_of_Z (Qc_trunc (Qcmult q scale))) scale))
    else Num_Z (Qc_trunc (Qcdiv q scale) * Z.pow 10 (Z.opp d))
  end.

Definition num_floor a := match a with Num_Z _ => a | Num_Q q => Num_Z (Qc_floor q) end.
Definition num_ceil a := match a with Num_Z _ => a | Num_Q q => Num_Z (Qc_ceiling q) end.

Definition num_power a b : option num :=
  match a, b with
  | Num_Z x, Num_Z y => match Zpower_opt x y with Some z => Some (Num_Z z) | None => None end
  | _, _ => match Qcpower_opt (Qc_of_num a) (Qc_of_num b) with Some q => Some (Num_Q q) | None => None end
  end.

(** A function of numbers; NULL as soon as one of the arguments is NULL. [conv] reads
    the arguments, [f] computes. *)
Definition num_fun2 (conv : value -> option num) (f : num -> num -> option num) 
           (l : list value) : value :=
  match l with
  | v1 :: v2 :: nil =>
    match conv v1, conv v2 with
    | Some a, Some b => match f a b with Some n => value_of_num n | None => Value_Z None end
    | _, _ => Value_Z None
    end
  | _ => Value_Z None
  end.

Definition num_fun1 (conv : value -> option num) (f : num -> num) (l : list value) : value :=
  match l with
  | v1 :: nil => match conv v1 with Some a => value_of_num (f a) | None => Value_Z None end
  | _ => Value_Z None
  end.

(** * Decimal scales

    MySQL and OceanBase compute the quotient of two numbers, and the average, as decimal
    numbers whose scale is the scale of the dividend, increased by [div_precision_increment]
    (4 by default); the result is rounded, ties away from zero. The scale of a number is the
    number of decimals it needs; the declared scale of a column is not known. *)

(** the number of decimals of [q], at most 40 *)
Definition dec_scale (q : Qc) : nat :=
  let d := Zpos (Qden q) in
  match find (fun s => Z.eqb (Z.modulo (Z.pow 10 (Z.of_nat s)) d) 0) (seq 0 41) with
  | Some s => s
  | None => 40%nat
  end.

Definition num_scale (n : num) : nat := match n with Num_Z _ => 0%nat | Num_Q q => dec_scale q end.

Definition round_scale (q : Qc) (s : nat) : Qc :=
  let m := Qc_of_Z (Z.pow 10 (Z.of_nat s)) in
  Qcdiv (Qc_of_Z (Qc_round (Qcmult q m))) m.

Definition num_div_dec (incr : nat) (a b : num) : option num :=
  if num_is_zero b then None
  else Some (Num_Q (round_scale (Qcdiv (Qc_of_num a) (Qc_of_num b)) (num_scale a + incr)%nat)).

(** * Strings *)

(** [string_repeat] and [string_of_Z] are those of [Values.v]. *)
Definition pad_zeros (width : nat) (s : string) : string :=
  string_repeat (width - String.length s) "0" ++ s.

(** The text of a decimal number, with the decimals it needs: [12.466], [-0.5], [3]. *)
Definition string_of_dec (q : Qc) : string :=
  let sc := dec_scale q in
  let m := Z.pow 10 (Z.of_nat sc) in
  let scaled := (Qnum q * (m / Zpos (Qden q)))%Z in
  let ip := (Z.abs scaled / m)%Z in
  let fp := (Z.abs scaled mod m)%Z in
  (if Z.ltb scaled 0 then "-" else "") ++ string_of_Z ip
  ++ (if Nat.eqb sc 0%nat then "" else "." ++ pad_zeros sc (string_of_Z fp)).

Definition lower_s := string_map lower_ascii.
Definition upper_s := string_map upper_ascii.

(** The text of a value, as the dialects which convert implicitly write it. *)
Definition text_of (v : value) : option string :=
  match v with
  | Value_string s => s
  | Value_Z (Some z) => Some (string_of_Z z)
  | Value_I (Some (z, _)) => Some (string_of_Z z)
  | Value_Q (Some q) => Some (string_of_dec q)
  | Value_D (Some (q, _, s)) => Some (dec_text q s)
  (* a float, as the MySQL family prints it ([my_gcvt]) *)
  | Value_F (Some (x, k)) => Some (my_text (fmt_of (Nat.odd k)) (special_of_tag (Nat.div k 2)) x)
  | Value_bool (Some b) => Some (if b then "1" else "0")
  | _ => None
  end.

(** [LIKE]: [%] and [_] are the wildcards; [esc] is the escape character, if any. *)
Fixpoint like_gen (esc : option ascii) (p : string) : string -> bool :=
  match p with
  | EmptyString => fun s => match s with EmptyString => true | _ => false end
  | String c p' =>
    if match esc with Some e => Ascii.eqb c e | None => false end
    then match p' with
         | String c2 p'' =>
           fun s => match s with
                    | EmptyString => false
                    | String c' s' => Ascii.eqb c2 c' && like_gen esc p'' s'
                    end
         | EmptyString => fun _ => false
         end
    else if Ascii.eqb c "%" 
         then fix star (s : string) : bool :=
                like_gen esc p' s || match s with EmptyString => false | String _ s' => star s' end
         else if Ascii.eqb c "_" 
              then fun s => match s with EmptyString => false | String _ s' => like_gen esc p' s' end
              else fun s => match s with
                            | EmptyString => false
                            | String c' s' => Ascii.eqb c c' && like_gen esc p' s'
                            end
  end.

Definition string_index (sub s : string) : Z :=
  match String.index 0 sub s with Some i => Z.of_nat (S i) | None => 0%Z end.

(** [SUBSTRING] with the conventions of MySQL: a negative start counts from the end,
    and 0 gives the empty string. *)
Definition substr_from_end (s : string) (start : Z) (len : option Z) : string :=
  let total := Z.of_nat (String.length s) in
  if (start =? 0)%Z then EmptyString
  else let st := if (0 <? start)%Z then start else (total + start + 1)%Z in
       match len with
       | Some l => if (l <=? 0)%Z then EmptyString else sql_substring s st (Some l)
       | None => sql_substring s st None
       end.

(** * Generic tables of predicates

    The comparison [cmp] returns [None] when it is not defined (NULL, or no
    comparison between the values). *)

Definition cmp_pred (cmp : value -> value -> option comparison) (test : comparison -> bool) :=
  binary3 (fun a b => match cmp a b with Some c => bool3_of_bool (test c) | None => unknown3 end).

Definition le_pred (cmp : value -> value -> option comparison) (a b : value) : bool3 :=
  match cmp a b with Some c => bool3_of_bool (negb (is_Gt c)) | None => unknown3 end.

Definition between_gen (cmp : value -> value -> option comparison) (l : list value) :=
  match l with
  | x :: lo :: hi :: nil => andb3 (le_pred cmp lo x) (le_pred cmp x hi)
  | _ => unknown3
  end.

Definition in_gen (cmp : value -> value -> option comparison) (l : list value) :=
  match l with
  | nil => unknown3
  | x :: l => fold_left (fun acc v => orb3 acc (match cmp x v with 
                                               | Some c => bool3_of_bool (is_Eq c) 
                                               | None => unknown3 end)) l false3
  end.

Fixpoint row_eq_gen (cmp : value -> value -> option comparison) (l1 l2 : list value) :=
  match l1, l2 with
  | nil, nil => true3
  | v1 :: l1, v2 :: l2 => 
    andb3 (match cmp v1 v2 with Some c => bool3_of_bool (is_Eq c) | None => unknown3 end) 
          (row_eq_gen cmp l1 l2)
  | _, _ => unknown3
  end.

(** The comparison predicates, [BETWEEN], [IN] and the row comparisons. *)
Definition comparison_table (cmp : value -> value -> option comparison) 
  : list (string * (list value -> bool3)) :=
     ("=", cmp_pred cmp is_Eq)
  :: ("<>", binary3 (fun a b => negb3 (cmp_pred cmp is_Eq (a :: b :: nil))))
  :: ("!=", binary3 (fun a b => negb3 (cmp_pred cmp is_Eq (a :: b :: nil))))
  :: ("<", cmp_pred cmp is_Lt)
  :: ("<=", cmp_pred cmp (fun c => negb (is_Gt c)))
  :: (">", cmp_pred cmp is_Gt)
  :: (">=", cmp_pred cmp (fun c => negb (is_Lt c)))
  :: ("between", between_gen cmp)
  :: ("not between", fun l => negb3 (between_gen cmp l))
  :: ("in", in_gen cmp)
  :: ("not in", fun l => negb3 (in_gen cmp l))
  :: ("row=", fun l => let (l1, l2) := split_half l in row_eq_gen cmp l1 l2)
  :: ("row<>", fun l => let (l1, l2) := split_half l in negb3 (row_eq_gen cmp l1 l2))
  :: nil.

(** * Generic aggregates *)

Definition non_nulls_by (isnull : value -> bool) (l : list value) := filter (fun v => negb (isnull v)) l.

Definition agg_extremum_by (isnull : value -> bool) (order : value -> value -> comparison)
           (keep : comparison -> bool) (l : list value) :=
  match non_nulls_by isnull l with
  | nil => Value_Z None
  | v :: l' => fold_left (fun a b => if keep (order a b) then a else b) l' v
  end.

Definition agg_count_by (isnull : value -> bool) (l : list value) :=
  Value_Z (Some (Z.of_nat (List.length (non_nulls_by isnull l)))).

(** Sums, in the numbers which [conv] reads; the sum of nothing is NULL. *)
Definition agg_sum_by (isnull : value -> bool) (conv : value -> option num) (l : list value) :=
  match flat_map (fun v => match conv v with Some n => n :: nil | None => nil end) (non_nulls_by isnull l) with
  | nil => Value_Z None
  | n :: ns => value_of_num (fold_left num_plus ns n)
  end.

Definition agg_avg_by (isnull : value -> bool) (conv : value -> option num) (l : list value) :=
  match flat_map (fun v => match conv v with Some n => n :: nil | None => nil end) (non_nulls_by isnull l) with
  | nil => Value_Q None
  | n :: ns => 
    Value_Q (Some (Qcdiv (Qc_of_num (fold_left num_plus ns n)) 
                         (Qc_of_Z (Z.of_nat (S (List.length ns))))))
  end.

(** the average, as a decimal number of the scale of its arguments plus [incr] *)
Definition agg_avg_dec (incr : nat) (isnull : value -> bool) (conv : value -> option num) (l : list value) :=
  match flat_map (fun v => match conv v with Some n => n :: nil | None => nil end) (non_nulls_by isnull l) with
  | nil => Value_Q None
  | n :: ns => 
    let sc := fold_left (fun m x => Nat.max m (num_scale x)) ns (num_scale n) in
    Value_Q (Some (round_scale (Qcdiv (Qc_of_num (fold_left num_plus ns n)) 
                                      (Qc_of_Z (Z.of_nat (S (List.length ns))))) (sc + incr)%nat))
  end.

Definition agg_concat_by (isnull : value -> bool) (sep : string) (l : list value) :=
  match flat_map (fun v => match text_of v with Some s => s :: nil | None => nil end) (non_nulls_by isnull l) with
  | nil => Value_string None
  | s :: ss => Value_string (Some (fold_left (fun acc x => acc ++ sep ++ x) ss s))
  end.

(** The aggregate of [E_AggX] with a separator: the argument is the list [v1, sep1, v2, sep2, ...]
    of the sorted rows. The NULL values are ignored, and the separator which precedes a value is
    that of its row (a NULL separator is [default]). *)
Fixpoint concat_pairs (isnull : value -> bool) (default : string) (first : bool) (l : list value) : string :=
  match l with
  | v :: s :: r =>
    if isnull v then concat_pairs isnull default first r
    else match text_of v with
         | None => concat_pairs isnull default first r
         | Some t => 
           (if first then "" else match text_of s with Some x => if isnull s then default else x | None => default end) ++ t ++
           concat_pairs isnull default false r
         end
  | _ => ""
  end.

Fixpoint firsts (l : list value) : list value :=
  match l with v :: _ :: r => v :: firsts r | _ => nil end.

Definition agg_concat_sep_by (isnull : value -> bool) (default : string) (l : list value) :=
  if forallb isnull (firsts l) then Value_string None
  else Value_string (Some (concat_pairs isnull default true l)).

(** the first [n] characters of a string (the length limit of [GROUP_CONCAT]) *)
Definition truncate_text (n : N) (v : value) : value :=
  match v with
  | Value_string (Some s) => 
    if N.leb (N.of_nat (String.length s)) n then v else Value_string (Some (String.substring 0 (N.to_nat n) s))
  | _ => v
  end.

(** * The decimal arithmetic of the MySQL family

    MySQL, MariaDB, TiDB, Percona, PolarDB and OceanBase share the decimal library of MySQL
    ([strings/decimal.c]): a decimal holds its digits by units of 9 ([DIG_PER_DEC1]). An operand
    is an integer, a decimal, or a string, which an arithmetic operation converts to a
    floating-point number (the former [lenient] path is kept for it). *)
Inductive mnum : Type :=
  | MI : Z -> mnum
  | MD : Qc -> nat -> nat -> mnum
  | MO : mnum.

Definition mclass (v : value) : option mnum :=
  match v with
  | Value_Z (Some z) => Some (MI z)
  | Value_I (Some (z, _)) => Some (MI z)
  | Value_bool (Some b) => Some (MI (if b then 1%Z else 0%Z))
  | Value_D (Some (q, f, s)) => Some (MD q f s)
  | Value_Q (Some q) => Some (MD q (dec_scale q) (dec_scale q))
  | Value_string (Some _) => Some MO
  | Value_F (Some _) => Some MO
  | _ => None
  end.

Definition mdec (m : mnum) : Qc * nat * nat :=
  match m with
  | MI z => (Qc_of_Z z, 0%nat, 0%nat)
  | MD q f s => (q, f, s)
  | MO => (Qc_of_Z 0, 0%nat, 0%nat)
  end.

(** [DECIMAL_MAX_SCALE] of MySQL *)
Definition my_max_scale : nat := 30.

Definition roundup9 (n : nat) : nat := (Nat.div (n + 8) 9 * 9)%nat.

(** [+], [-]: the digits held and the scale are the larger ones ([do_add], [Item_func_additive_op]) *)
Definition my_dplus (a b : Qc * nat * nat) : value :=
  let '(q1, f1, s1) := a in let '(q2, f2, s2) := b in VDec (Qcplus q1 q2) (Nat.max f1 f2) (Nat.max s1 s2).
Definition my_dminus (a b : Qc * nat * nat) : value :=
  let '(q1, f1, s1) := a in let '(q2, f2, s2) := b in VDec (Qcminus q1 q2) (Nat.max f1 f2) (Nat.max s1 s2).
(** [*]: the sums ([decimal_mul], [Item_func_mul::result_precision]) *)
Definition my_dmult (a b : Qc * nat * nat) : value :=
  let '(q1, f1, s1) := a in let '(q2, f2, s2) := b in 
  VDec (Qcmult q1 q2) (f1 + f2) (Nat.min (s1 + s2) my_max_scale).

(** [/] ([do_div_mod]): the quotient holds [ROUND_UP(frac1 + frac2 + scale_incr)] units of 9 digits,
    where [frac1], [frac2] are the digits of the operands rounded up to units and [scale_incr] is
    [div_precision_increment] less the digits added by this rounding; the digits are those of the
    long division, truncated. It is displayed with the scale of the dividend plus
    [div_precision_increment] ([Item_func_div::fix_length_and_dec_decimal]), rounded. A division
    by zero is NULL. *)
Definition my_ddiv (incr : nat) (a b : Qc * nat * nat) : value :=
  let '(q1, f1, s1) := a in let '(q2, f2, s2) := b in
  if Qc_is_zero q2 then Value_D None
  else 
    let r1 := roundup9 f1 in
    let r2 := roundup9 f2 in
    let inc := Z.to_nat (Z.max 0 (Z.of_nat incr - Z.of_nat (r1 - f1) - Z.of_nat (r2 - f2))) in
    let f := roundup9 (r1 + r2 + inc) in
    VDec (dec_trunc (Qcdiv q1 q2) f) f (Nat.min (s1 + incr) my_max_scale).

(** A result of the double arithmetic: the exact result rounded to binary64; an overflow is an error
    ([DOUBLE value is out of range], [ER_DATA_OUT_OF_RANGE]). *)
Definition my_double (v : value) : value :=
  let dbl q := match round_q binary64 q with
               | (F_PosInf, _) | (F_NegInf, _) => Value_Err "DOUBLE value is out of range"
               | r => VF false r
               end in
  match v with
  | Value_Q (Some q) => dbl q
  | Value_Z (Some z) => dbl (Qc_of_Z z)
  | Value_D (Some (q, _, _)) => dbl q
  | Value_Q None | Value_Z None | Value_D None => Value_F None
  | _ => v
  end.

(** [fi] is the operation on integers, if the result of two integers is an integer *)
Definition my_arith2 (fi : option (Z -> Z -> Z)) (fd : Qc * nat * nat -> Qc * nat * nat -> value)
           (other : list value -> value) (l : list value) : value :=
  match l with
  | v1 :: v2 :: nil =>
    match mclass v1, mclass v2, fi with
    (* [BIGINT] arithmetic; unsigned when an operand is [BIGINT UNSIGNED]; out of range is an error
       ([ER_DATA_OUT_OF_RANGE], [Item_func_plus::int_op], ...) *)
    | Some (MI a), Some (MI b), Some f => 
      let r := f a b in
      let unsigned := existsb (fun v => match v with Value_I (Some (_, 1%nat)) => true | _ => false end) l in
      if unsigned 
      then (if int_range_ok 1 r then Value_I (Some (r, 1%nat)) else Value_Err "BIGINT UNSIGNED value is out of range")
      else (if int_range_ok 64 r then Value_Z (Some r) else Value_Err "BIGINT value is out of range")
    | _, _, _ =>
    match mclass v1, mclass v2 with
    (* each operand is converted to a double, then the operation is done on doubles *)
    | Some MO, Some _ | Some _, Some MO => 
      my_double (other (map (fun v => match lenient v with Some n => my_double (value_of_num n) | None => v end) l))
    | Some m1, Some m2 => fd (mdec m1) (mdec m2)
    | _, _ => other l
    end
    end
  | _ => other l
  end.

(** [ROUND(x, d)], [TRUNCATE(x, d)] of a decimal: a decimal of scale [d] *)
Definition my_dround (trunc : bool) (q : Qc) (d : Z) : value :=
  if Z.leb 0 d 
  then VDec ((if trunc then dec_trunc else dec_round) q (Z.to_nat d)) (Z.to_nat d) (Z.to_nat d)
  else let m := Qc_of_Z (pow10 (Z.to_nat (Z.opp d))) in
       VDec (Qcmult (Qc_of_Z ((if trunc then Qc_trunc else Qc_round) (Qcdiv q m))) m) 0 0.

(** [SUM] of decimals: the larger scale; [AVG]: the division of the sum by the count *)
Definition my_dsum (isnull : value -> bool) (l : list value) : option (Qc * nat * nat) :=
  let ms := flat_map (fun v => match mclass v with Some (MI z) => MI z :: nil | Some (MD q f s) => MD q f s :: nil | _ => nil end)
                     (non_nulls_by isnull l) in
  match ms with
  | nil => None
  | m :: r => Some (fold_left (fun acc x => let '(q1, f1, s1) := acc in let '(q2, f2, s2) := mdec x in
                                          (Qcplus q1 q2, Nat.max f1 f2, Nat.max s1 s2)) r (mdec m))
  end.

Definition has_decimal (isnull : value -> bool) (l : list value) : bool :=
  existsb (fun v => match v with Value_D (Some _) | Value_Q (Some _) => true | _ => false end) (non_nulls_by isnull l).

Definition has_text (isnull : value -> bool) (l : list value) : bool :=
  existsb (fun v => match v with Value_string (Some _) | Value_F (Some _) => true | _ => false end) (non_nulls_by isnull l).

(** [SUM] and [AVG] of doubles: the values are added one by one, each sum being rounded
    ([Item_sum_sum::add] with a [double] result) *)
Definition my_dbl_sum (isnull : value -> bool) (l : list value) : option Qc :=
  match flat_map (fun v => match lenient v with Some n => n :: nil | None => nil end) (non_nulls_by isnull l) with
  | nil => None
  | n :: ns => Some (fold_left (fun acc x => snd (round_q binary64 (Qcplus acc (Qc_of_num x)))) ns 
                               (snd (round_q binary64 (Qc_of_num n))))
  end.

Definition my_agg_sum (isnull : value -> bool) (l : list value) : value :=
  if has_text isnull l 
  then match my_dbl_sum isnull l with Some q => my_double (Value_Q (Some q)) | None => Value_F None end
  else if negb (has_decimal isnull l) then agg_sum_by isnull lenient l
  else match my_dsum isnull l with Some (q, f, s) => VDec q f s | None => Value_D None end.

Definition my_agg_avg (incr : nat) (isnull : value -> bool) (l : list value) : value :=
  if has_text isnull l 
  then match my_dbl_sum isnull l with 
       | Some q => my_double (Value_Q (Some (Qcdiv q (Qc_of_Z (Z.of_nat (List.length (non_nulls_by isnull l)))))))
       | None => Value_F None end
  else match my_dsum isnull l with
       | Some d => my_ddiv incr d (Qc_of_Z (Z.of_nat (List.length (non_nulls_by isnull l))), 0%nat, 0%nat)
       | None => Value_D None
       end.

(** [CAST(x AS DECIMAL(p, s))] in the MySQL family: rounded to [s] decimals, ties away from zero; a value
    out of the range of the type is the largest value of the type ([my_decimal2decimal] with
    [E_DEC_OVERFLOW], a warning in a [SELECT]) *)
Definition my_cast_decimal (p s : Z) (v : value) : value :=
  match lenient v with
  | Some n =>
    let s' := Z.to_nat s in
    let r := dec_round (Qc_of_num n) s' in
    let mx := Qcminus (Qc_of_Z (Z.pow 10 (p - s))) (Qcdiv (Qc_of_Z 1) (Qc_of_Z (Z.pow 10 s))) in
    let r := match Qccompare r mx with Gt => mx | _ => match Qccompare r (Qcopp mx) with Lt => Qcopp mx | _ => r end end in
    VDec r s' s'
  | None => Value_D None
  end.

(** variance, population or sample *)
Definition agg_var_by (isnull : value -> bool) (conv : value -> option num) (sample : bool) (l : list value) :=
  let ns := flat_map (fun v => match conv v with Some n => n :: nil | None => nil end) (non_nulls_by isnull l) in
  let n := Qc_of_Z (Z.of_nat (List.length ns)) in
  match ns with
  | nil => Value_Q None
  | n1 :: rest =>
    let s := Qc_of_num (fold_left num_plus rest n1) in
    let s2 := Qc_of_num (fold_left num_plus (map (fun x => num_mult x x) rest) (num_mult n1 n1)) in
    let num := Qcminus s2 (Qcdiv (Qcmult s s) n) in
    let den := if sample then Qcminus n (Qc_of_Z 1) else n in
    if Qc_is_zero den then Value_Q None else Value_Q (Some (Qcdiv num den))
  end.

Definition agg_bit_by (isnull : value -> bool) (op : Z -> Z -> Z) (l : list value) :=
  match flat_map (fun v => match v with Value_Z (Some z) => z :: nil | _ => nil end) (non_nulls_by isnull l) with
  | nil => Value_Z None
  | z :: zs => Value_Z (Some (fold_left op zs z))
  end.

(** * Lookup in a table *)

Definition table_of_list (A : Type) (l : list (string * A)) : string -> option A :=
  fun s => string_assoc A s l.
Arguments table_of_list {A}.
