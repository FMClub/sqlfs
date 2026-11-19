(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**                 Building blocks for the value semantics of dialects             *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String Ascii ZArith NArith QArith Qcanon Qround.

Require Import Bool3 OrderedSet Values.

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
  | Value_Q (Some q) => Some (string_of_dec q)
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
