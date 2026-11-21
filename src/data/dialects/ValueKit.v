(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**                 Building blocks for the value semantics of dialects             *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String Ascii ZArith NArith QArith Qcanon Qround.

Require Import Bool3 OrderedSet IEEE Temporal Json Values.

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
  (* an exponent: [e] or [E], a sign, digits (MySQL reads ['123e-2'] as 1.23); bounded by 400 so that
     [10 ^ e] stays small (a longer exponent is not read) *)
  let '(ex, r'') := match r' with
                    | String c r3 =>
                      if (Ascii.eqb c "e"%char || Ascii.eqb c "E"%char) && negb (Nat.eqb (ni + nf)%nat 0%nat) then
                        let '(eneg, r4) := match r3 with
                                           | String "-" r5 => (true, r5) | String "+" r5 => (false, r5)
                                           | _ => (false, r3) end in
                        let '(ev, ne, r6) := digits_aux r4 0%Z 0%nat in
                        if Nat.eqb ne 0%nat || Z.ltb 400 ev then (0%Z, r') else ((if eneg then Z.opp ev else ev), r6)
                      else (0%Z, r')
                    | EmptyString => (0%Z, r')
                    end in
  let mant := Q2Qc (Qmake (sgn (iv * Z.pow 10 (Z.of_nat nf) + fv)) (Z.to_pos (Z.pow 10 (Z.of_nat nf)))) in
  let n := if Z.eqb ex 0 then
             (if Nat.eqb nf 0%nat then Num_Z (sgn iv) else Num_Q mant)
           else if Z.ltb 0 ex then Num_Q (Qcmult mant (Q2Qc (inject_Z (Z.pow 10 ex))))
           else Num_Q (Qcdiv mant (Q2Qc (inject_Z (Z.pow 10 (Z.opp ex))))) in
  (n, if Nat.eqb (ni + nf)%nat 0%nat then false else if String.eqb (string_rtrim r'') EmptyString then true else false).

Definition parse_prefix s : num := fst (parse_number s).

(** Numbers, with booleans as 0 and 1, and strings read leniently. *)
Definition lenient (v : value) : option num :=
  match v with
  | Value_Z (Some z) => Some (Num_Z z)
  | Value_Q (Some q) => Some (Num_Q q)
  | Value_D (Some (q, _, _)) => Some (Num_Q q)
  | Value_F (Some (q, k)) => if Nat.leb (Nat.div (Nat.modulo k 10) 2) 1 then Some (Num_Q q) else None
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
  | Value_F (Some (q, k)) => if Nat.leb (Nat.div (Nat.modulo k 10) 2) 1 then Some (Num_Q q) else None
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
  (* a negative exponent gives a rational: [POWER (4, -2)] is [0.0625] *)
  | Num_Z x, Num_Z y =>
    if Z.leb 0 y then match Zpower_opt x y with Some z => Some (Num_Z z) | None => None end
    else match Qcpower_opt (Qc_of_num a) (Qc_of_num b) with Some q => Some (Num_Q q) | None => None end
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
(** the exponents of 2 and of 5 in [d], and what remains *)
Fixpoint factor25 (fuel : nat) (d : Z) (a b : nat) : nat * nat * Z :=
  match fuel with
  | O => (a, b, d)
  | S f => if Z.eqb (Z.modulo d 2) 0 then factor25 f (d / 2) (S a) b
           else if Z.eqb (Z.modulo d 5) 0 then factor25 f (d / 5) a (S b)
           else (a, b, d)
  end.

(** the number of decimals of [q]: exact when its expansion terminates ([d = 2^a 5^b]: [max a b]
    decimals), 40 otherwise (then rounded) *)
Definition dec_scale (q : Qc) : nat :=
  let '(a, b, r) := factor25 (Pos.size_nat (Qden q)) (Zpos (Qden q)) 0 0 in
  if Z.eqb r 1 then Nat.max a b else 40%nat.

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
  let d := Zpos (Qden q) in
  (* exact when the expansion terminates; rounded half away from zero otherwise *)
  let scaled := (Z.sgn (Qnum q) * ((Z.abs (Qnum q) * m * 2 + d) / (2 * d)))%Z in
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
  (* a double with fixed decimals is printed with them ([String::set_real] with [decimals] < [NOT_FIXED_DEC]) *)
  | Value_F (Some (x, k)) => 
    match fdec v with
    | Some d => Some (dec_text x d)
    | None => Some (my_text (fmt_of (Nat.odd k)) (special_of_tag (Nat.div (Nat.modulo k 10) 2)) x)
    end
  | Value_T (Some (n, k)) => 
    let fsp := Nat.div k 10 in
    match Nat.modulo k 10 with
    | 0%nat => Some (date_text n) | 1%nat => Some (time_text n fsp) | _ => Some (timestamp_text n fsp) end
  | Value_C (Some (s, _)) => Some s
  | Value_J (Some (t, 2%nat)) => Some (array_text t)
  (* PostgreSQL [json]: the text as it was given (only [jsonb] is normalized) *)
  | Value_J (Some (t, 1%nat)) => Some t
  | Value_J (Some (t, _)) => match parse_json t with Some j => Some (text_spaced j) | None => Some t end
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

(** [(a1, ..., an) < (b1, ..., bn)] (TODO 3.7): the first pair which is not equal decides; a NULL before
    the decision makes the result UNKNOWN; equal rows are [=]. [strict]: [<] (or [>]), [lt]: [<] / [<=]. *)
Fixpoint row_cmp_gen (cmp : value -> value -> option comparison) (lt strict : bool) (l1 l2 : list value) : bool3 :=
  match l1, l2 with
  | nil, nil => bool3_of_bool (negb strict)
  | v1 :: r1, v2 :: r2 =>
    match cmp v1 v2 with
    | Some Eq => row_cmp_gen cmp lt strict r1 r2
    | Some Lt => bool3_of_bool lt
    | Some Gt => bool3_of_bool (negb lt)
    | None => unknown3
    end
  | _, _ => unknown3
  end.

(** [(a1, ..., an) IS NULL]: all are NULL; [IS NOT NULL]: none is *)
Definition row_preds (cmp : value -> value -> option comparison) (isnull : value -> bool)
  : list (string * (list value -> bool3)) :=
     ("row<", fun l => let (l1, l2) := split_half l in row_cmp_gen cmp true true l1 l2)
  :: ("row<=", fun l => let (l1, l2) := split_half l in row_cmp_gen cmp true false l1 l2)
  :: ("row>", fun l => let (l1, l2) := split_half l in row_cmp_gen cmp false true l1 l2)
  :: ("row>=", fun l => let (l1, l2) := split_half l in row_cmp_gen cmp false false l1 l2)
  :: ("row is null", fun l => bool3_of_bool (forallb isnull l))
  :: ("row is not null", fun l => bool3_of_bool (forallb (fun v => negb (isnull v)) l))
  :: nil.

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
  :: row_preds cmp is_null.

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

(** * Dates and times of the MySQL family ([sql/sql_time.cc], [sql/item_timefunc.cc])

    A temporal value used as a number is [YYYYMMDD] for a [DATE], [YYYYMMDDhhmmss] for a [DATETIME] or a
    [TIMESTAMP], [hhmmss] for a [TIME], with the fractional seconds as decimals ([TIME_to_ulonglong]). *)
Definition my_temporal_number (v : value) : option (Qc * nat) :=
  match temporal_parts v with
  | Some (k, n, fsp) =>
    let ymd d := let '(y, m, dd) := civil_from_days d in y * 10000 + m * 100 + dd in
    let hms u := let s := u / 1000000 in (s / 3600) * 10000 + ((s / 60) mod 60) * 100 + s mod 60 in
    let frac u := Qcdiv (Qc_of_Z (u mod 1000000)) (Qc_of_Z 1000000) in
    match k with
    | 0%nat => Some (Qc_of_Z (ymd n), 0%nat)
    | 1%nat => Some (Qcplus (Qc_of_Z (hms n)) (frac n), fsp)
    | _ => Some (Qcplus (Qc_of_Z (ymd (ts_days n) * 1000000 + hms (ts_usec n))) (frac (ts_usec n)), fsp)
    end
  | None => None
  end.

(** a number compared with a date or a datetime is read as one ([number_to_datetime], [sql-common/my_time.cc]):
    [YYMMDD] (2000-2069 below 70), [YYYYMMDD], [YYMMDDhhmmss], [YYYYMMDDhhmmss] *)
Definition my_number_to_datetime (n : Z) : option Z :=
  let ymd (x : Z) := let y := x / 10000 in let m := (x / 100) mod 100 in let d := x mod 100 in
                     if valid_date y m d then Some (days_from_civil y m d) else None in
  let ymdhms (x : Z) := match ymd (x / 1000000) with
                        | Some days => let t := x mod 1000000 in
                                       let h := t / 10000 in let mi := (t / 100) mod 100 in let s := t mod 100 in
                                       if (h <? 24) && (mi <? 60) && (s <? 60) then Some (ts_of days (((h * 60 + mi) * 60 + s) * 1000000)) else None
                        | None => None end in
  if n <? 101 then None
  else if n <=? 691231 then option_map (fun d => ts_of d 0) (ymd (n + 20000000))
  else if n <? 700101 then None
  else if n <=? 991231 then option_map (fun d => ts_of d 0) (ymd (n + 19000000))
  else if n <? 10000101 then None
  else if n <=? 99991231 then option_map (fun d => ts_of d 0) (ymd n)
  else if n <? 101000000 then None
  else if n <=? 691231235959 then ymdhms (n + 20000000000000)
  else if n <? 700101000000 then None
  else if n <=? 991231235959 then ymdhms (n + 19000000000000)
  else ymdhms n.

Definition my_temporal_text (v : value) : option string :=
  match temporal_parts v with
  | Some (0%nat, d, _) => Some (date_text d)
  | Some (1%nat, u, f) => Some (time_text u f)
  | Some (_, t, f) => Some (timestamp_text t f)
  | None => None
  end.

(** a date, a datetime, or a string which is one, as a timestamp (and whether it has a time) *)
Definition my_ts_of (v : value) : option (Z * bool) :=
  match v with
  | Value_string (Some t) => 
    match parse_date t with Some d => Some (ts_of d 0, false) | None =>
    match parse_timestamp t with Some x => Some (x, true) | None =>
    (* a string of digits is read as a number: [YYMMDD], [YYYYMMDD], [YYMMDDhhmmss], [YYYYMMDDhhmmss]
       ([str_to_datetime] of [sql-common/my_time.cc]) *)
    let cs := list_ascii_of_string t in
    let n := List.length cs in
    if forallb (fun c => let k := Ascii.nat_of_ascii c in Nat.leb 48 k && Nat.leb k 57) cs
       && (Nat.eqb n 6 || Nat.eqb n 8 || Nat.eqb n 12 || Nat.eqb n 14)
    then match Z_of_string t with
         | Some z => match my_number_to_datetime z with Some x => Some (x, Nat.ltb 8 n) | None => None end
         | None => None end
    else None end end
  | _ => match temporal_parts v with
         | Some (0%nat, d, _) => Some (ts_of d 0, false)
         | Some (1%nat, _, _) => None
         | Some (_, t, _) => Some (t, true)
         | None => None end
  end.

(** [DATE_ADD(d, INTERVAL n unit)]: a [DATE] when [d] is a date and the unit is a day or longer, a
    [DATETIME] otherwise; a date out of [0001-01-01 .. 9999-12-31] is NULL *)
(** the integer which a string starts with ([val_int] of a string: the rest is ignored, with a warning) *)
Definition my_int_prefix (t : string) : Z :=
  let t := string_ltrim t in
  let '(neg, t) := match t with String "-" r => (true, r) | String "+" r => (false, r) | _ => (false, t) end in
  let fix take (l : list ascii) : list ascii :=
      match l with c :: r => if match digit c with Some _ => true | None => false end then c :: take r else nil | nil => nil end in
  let z := match digits_of (string_of_list_ascii (take (list_ascii_of_string t))) with Some z => z | None => 0%Z end in
  if neg then (- z)%Z else z.

Definition my_date_add (sign : Z) (v iv : value) : value :=
  match my_ts_of v, iv with
  | Some (t, has_time), Value_V (Some (mo, d, us)) =>
    let r := ts_plus_interval t (sign * mo, sign * d, sign * us) in
    let '(y, _, _) := civil_from_days (ts_days r) in
    if negb ((1 <=? y) && (y <=? 9999))%Z then Value_T None
    (* an interval with a fraction of a second gives 6 fractional digits *)
    else if has_time || negb (Z.eqb us 0)
         then VTs r (if negb (Z.eqb (us mod 1000000) 0) then 6%nat
                     else match temporal_parts v with Some (_, _, f) => f | None => 0%nat end)
    else VDate (ts_days r)
  | _, _ => Value_T None
  end.

(** [WEEK(d)] with the default mode 0: weeks start on Sunday, week 1 is the first one with a Sunday *)
Definition my_week0 (days : Z) : Z :=
  let '(y, _, _) := civil_from_days days in
  let jan1 := days_from_civil y 1 1 in
  let first_sunday := jan1 + (7 - day_of_week jan1) mod 7 in
  if days <? first_sunday then 0 else (days - first_sunday) / 7 + 1.

(** [TIMESTAMPDIFF(unit, a, b)]: the number of whole units from [a] to [b] *)
Definition my_months_between (a b : Z) : Z :=
  (* whole months: the day and the time of [b] must reach those of [a] *)
  let '(ya, ma, da) := civil_from_days (ts_days a) in
  let '(yb, mb, db) := civil_from_days (ts_days b) in
  let m := (yb * 12 + mb) - (ya * 12 + ma) in
  let ka := da * usec_per_day + ts_usec a in
  let kb := db * usec_per_day + ts_usec b in
  if (0 <? m) && (kb <? ka) then m - 1 else if (m <? 0) && (ka <? kb) then m + 1 else m.

Definition my_timestampdiff (unit : string) (a b : Z) : option Z :=
  let d := b - a in
  match string_map upper_ascii unit with
  | "MICROSECOND" => Some d | "SECOND" => Some (Z.quot d 1000000) | "MINUTE" => Some (Z.quot d 60000000)
  | "HOUR" => Some (Z.quot d 3600000000) | "DAY" => Some (Z.quot d usec_per_day) | "WEEK" => Some (Z.quot d (7 * usec_per_day))
  | "MONTH" => Some (my_months_between a b) | "QUARTER" => Some (Z.quot (my_months_between a b) 3)
  | "YEAR" => Some (Z.quot (my_months_between a b) 12)
  | _ => None
  end%string.

Definition my_cast_temporal (kind : nat) (v : value) : value :=
  match v with
  | Value_string (Some t) =>
    let t := string_rtrim (string_ltrim t) in
    match kind with
    | 0%nat => match parse_date t with Some d => VDate d | None => 
               match parse_timestamp t with Some x => VDate (ts_days x) | None => Value_T None end end
    | 1%nat => match parse_time t with Some u => VTime u 0 | None => Value_T None end
    | _ => match parse_timestamp t with Some u => VTs u 0 | None => Value_T None end
    end
  | _ => match kind, my_ts_of v, temporal_parts v with
         | 0%nat, Some (x, _), _ => VDate (ts_days x)
         | 1%nat, Some (x, _), _ => VTime (ts_usec x) 0
         | 1%nat, None, Some (1%nat, u, f) => VTime u f
         | _, Some (x, _), _ => VTs x 0
         | _, _, _ => Value_T None end
  end.

(** The typed literals [TIMESTAMP '...'] and [TIME '...'] of the MySQL family ("Date and Time Literals"): a
    [TIMESTAMP] literal has a date and a time, whose fields are runs of digits separated by any punctuation
    (['2017@01@01 00~00~00']), and a fractional part after a dot; a literal which is not one is an error
    ("Incorrect datetime value", [ER_WRONG_VALUE]), where the cast gives NULL. *)
Definition is_dig (c : ascii) : bool := match digit c with Some _ => true | None => false end.

Fixpoint digit_runs (l : list ascii) (cur : list ascii) : list string :=
  match l with
  | nil => match cur with nil => nil | _ => (string_of_list_ascii (rev cur) :: nil) end
  | c :: r => if is_dig c then digit_runs r (c :: cur)
              else match cur with nil => digit_runs r nil | _ => string_of_list_ascii (rev cur) :: digit_runs r nil end
  end.

Definition my_lit_datetime (v : value) : value :=
  let bad := Value_Err "Incorrect datetime value" in
  match v with
  | Value_string (Some t) =>
    let t := string_rtrim (string_ltrim t) in
    match index 0 " " t with
    | Some i =>
      let d := substring 0 i t in
      let tm := string_ltrim (substring (S i) (String.length t - S i) t) in
      let (main, frac) := match index 0 "." tm with
                          | Some j => (substring 0 j tm, substring (S j) (String.length tm - S j) tm)
                          | None => (tm, EmptyString) end in
      let num (x : string) := match digits_of x with Some z => z | None => 0%Z end in
      match digit_runs (list_ascii_of_string d) nil, digit_runs (list_ascii_of_string main) nil with
      | y :: m :: dd :: nil, h :: mi :: rest =>
        let sec := match rest with x :: nil => Some x | nil => Some "0"%string | _ => None end in
        match sec with
        | Some x =>
          let canon := (pad 4 (num y) ++ "-" ++ pad 2 (num m) ++ "-" ++ pad 2 (num dd) ++ " " ++
                        pad 2 (num h) ++ ":" ++ pad 2 (num mi) ++ ":" ++ pad 2 (num x) ++
                        (match frac with EmptyString => EmptyString | _ => "." ++ frac end))%string in
          match parse_timestamp canon with
          | Some u => if forallb is_dig (list_ascii_of_string frac) then VTs u (Nat.min 6 (String.length frac)) else bad
          | None => bad
          end
        | None => bad
        end
      | _, _ => bad
      end
    | None => bad
    end
  | _ => if is_null v then Value_T None else bad
  end.

(** [TIME '[-][D ]hh:mm[:ss][.ffffff]'], ['D hh'], and without delimiters ['hhmmss'], ['mmss'], ['ss'] (at most 6
    digits; a longer run of digits is a date and time, which is not a [TIME] literal); the fraction is rounded to 6
    digits. *)
Definition my_lit_time (v : value) : value :=
  let bad := Value_Err "Incorrect time value" in
  match v with
  | Value_string (Some t0) =>
    let t := string_rtrim (string_ltrim t0) in
    let '(neg, t) := match t with String "-" r => (true, r) | _ => (false, t) end in
    let '(main, frac) := match index 0 "." t with
                         | Some j => (substring 0 j t, substring (S j) (String.length t - S j) t)
                         | None => (t, EmptyString) end in
    let '(days, hms) := match index 0 " " main with
                        | Some i => (Some (substring 0 i main), string_ltrim (substring (S i) (String.length main - S i) main))
                        | None => (None, main) end in
    let d := match days with Some x => digits_of x | None => Some 0%Z end in
    let parts := match map digits_of (split_at ":" hms) with
                 | Some n :: nil =>
                   match days with
                   | Some _ => Some (n, 0, 0)%Z
                   | None => if Nat.leb (String.length hms) 6 then Some (n / 10000, (n / 100) mod 100, n mod 100)%Z else None
                   end
                 | Some h :: Some m :: nil => Some (h, m, 0%Z)
                 | Some h :: Some m :: Some x :: nil => Some (h, m, x)
                 | _ => None
                 end in
    let fr := list_ascii_of_string frac in
    match d, parts with
    | Some dz, Some (h, m, x) =>
      if (m <? 60)%Z && (x <? 60)%Z && forallb is_dig fr then
        let six := string_of_list_ascii (firstn 6 (fr ++ repeat "0"%char 6)) in
        let up := match nth_error fr 6 with Some c => match digit c with Some z => (5 <=? z)%Z | None => false end | None => false end in
        let us := (((dz * 24 + h) * 3600 + m * 60 + x) * 1000000 +
                   (match digits_of six with Some z => z | None => 0 end) + (if up then 1 else 0))%Z in
        VTime (if neg then - us else us)%Z (Nat.min 6 (List.length fr))
      else bad
    | _, _ => bad
    end
  | _ => if is_null v then Value_T None else bad
  end.

(** * JSON in the MySQL family ([sql/item_jsonfunc.cc], [sql-common/json_dom.cc])

    A value becomes a JSON value as a number, a string, or [null]; a string argument which a function reads
    as a JSON document must be valid JSON ([ER_INVALID_JSON_TEXT_IN_PARAM]). *)
Definition my_json_of_value (v : value) : json :=
  if is_null v then JNull else
  match v with
  | Value_Z (Some z) | Value_I (Some (z, _)) => JNum (string_of_Z z)
  | Value_D (Some (q, _, sc)) => JNum (dec_text q sc)
  | Value_Q (Some q) => JNum (string_of_dec q)
  | Value_J _ => match json_of_J v with Some j => j | None => JNull end
  | _ => match text_of v with Some t => JStr t | None => JNull end
  end.

(** a JSON document argument: a JSON value, or a string which is the text of one *)
Definition my_json_doc (v : value) : option (option json) :=
  match v with
  | Value_J _ => Some (json_of_J v)
  | _ => if is_null v then Some None 
         else match v with
              (* only a string can be the text of a document: a number is an error ("Invalid data type for JSON
                 data in argument 1", [ER_INVALID_TYPE_FOR_JSON]) *)
              | Value_string (Some t) | Value_C (Some (t, _)) =>
                match parse_json t with Some j => Some (Some j) | None => None end
              | _ => None
              end
  end.

(** a path without wildcard nor range (the functions which change a document, [JSON_LENGTH], ...) *)
Definition my_path (t : string) : option (list step) :=
  match parse_wpath t with Some w => wpath_exact w | None => None end.

(** the values at a path of the MySQL family, and whether the path may have several *)
Definition my_seek (d : json) (t : string) : option (bool * list json) :=
  match parse_wpath t with
  | Some w => Some (match wpath_exact w with Some _ => false | None => true end,
                    seek (List.length w + json_size d + 1) w (normalize d))
  | None => None
  end.

(** [JSON_EXTRACT (doc, path, ...)]: the value at the path; with several paths, or a path with a wildcard or a
    range, the array of the values found; NULL if there is none or if an argument is NULL *)
Definition my_json_extract (l : list value) : value :=
  match l with
  | doc :: paths =>
    match my_json_doc doc with
    | None => Value_Err "Invalid JSON text in argument 1"
    | Some None => Value_J None
    | Some (Some d) =>
      if existsb is_null paths then Value_J None
      else let found := map (fun p => match text_of p with Some t => my_seek d t | None => None end) paths in
           if existsb (fun x => match x with None => true | _ => false end) found
           then Value_Err "Invalid JSON path expression"
           else let vals := flat_map (fun x => match x with Some (_, r) => r | None => nil end) found in
                let many := existsb (fun x => match x with Some (b, _) => b | None => false end) found
                            || Nat.ltb 1 (List.length paths) in
                match vals with
                | nil => Value_J None
                | v :: nil => VJ 0 (if many then JArr vals else v)
                | _ => VJ 0 (JArr vals)
                end
    end
  | nil => Value_J None
  end.

Definition my_json_unquote (v : value) : value :=
  match v with
  | Value_J _ => match json_of_J v with Some (JStr t) => Value_string (Some t) | Some j => Value_string (Some (text_spaced j)) | None => Value_string None end
  | _ => Value_string (text_of v)
  end.

Definition my_json_type_name (j : json) : string := json_type_name j.

(** a JSON scalar compared with a SQL value: a string, a number, [true] / [false] as 1 / 0 *)
Definition json_scalar (v : value) : value :=
  match v with
  | Value_J _ => match json_of_J v with
                 | Some (JStr t) => Value_string (Some t)
                 | Some (JNum t) => value_of_num (parse_prefix t)
                 | Some (JBool b) => Value_Z (Some (if b then 1 else 0))
                 | Some JNull => Value_Z None
                 | Some j => Value_string (Some (text_compact j))
                 | None => Value_Z None end
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
  | Value_T (Some _) => 
    match my_temporal_number v with
    | Some (q, 0%nat) => Some (MI (Qc_trunc q))
    | Some (q, f) => Some (MD q f f)
    | None => None end
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

(** the decimals of an operand of the double arithmetic: those of a double, 0 for an integer, the scale of a
    decimal, none for a string *)
Definition my_fdec (v : value) : option nat :=
  match v with
  | Value_F _ => fdec v
  | Value_Z (Some _) | Value_I (Some _) | Value_bool (Some _) => Some 0%nat
  | Value_D (Some (_, _, s)) => Some s
  | Value_Q (Some q) => Some (dec_scale q)
  | _ => None
  end.

Definition dec_max (a b : option nat) : option nat :=
  match a, b with Some x, Some y => Some (Nat.max x y) | _, _ => None end.
Definition dec_sum (a b : option nat) : option nat :=
  match a, b with Some x, Some y => Some (x + y)%nat | _, _ => None end.

(** the result [r] of a function of the integer [v] ([ABS], [ROUND] to tens): out of the range of [BIGINT], or of
    [BIGINT UNSIGNED] for an unsigned argument, it is an error ([ER_DATA_OUT_OF_RANGE]) *)
Definition my_int_range (v r : value) : value :=
  match v, r with
  | Value_I (Some (_, 1%nat)), (Value_Z (Some z) | Value_I (Some (z, _))) =>
    if int_range_ok 1 z then r else Value_Err "BIGINT UNSIGNED value is out of range"
  | (Value_Z (Some _) | Value_I (Some _)), (Value_Z (Some z) | Value_I (Some (z, _))) =>
    if int_range_ok 64 z then r else Value_Err "BIGINT value is out of range"
  | _, _ => r
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
  then match my_dbl_sum isnull l with 
       | Some q => with_fdec (match non_nulls_by isnull l with v :: _ => my_fdec v | nil => None end) (my_double (Value_Q (Some q)))
       | None => Value_F None end
  else if negb (has_decimal isnull l) then agg_sum_by isnull lenient l
  else match my_dsum isnull l with Some (q, f, s) => VDec q f s | None => Value_D None end.

Definition my_agg_avg (incr : nat) (isnull : value -> bool) (l : list value) : value :=
  if has_text isnull l 
  then match my_dbl_sum isnull l with 
       (* [AVG] of doubles has the decimals of its argument plus [div_precision_increment] *)
       | Some q => with_fdec (match non_nulls_by isnull l with v :: _ => match my_fdec v with Some d => Some (d + incr)%nat | None => None end | nil => None end)
                             (my_double (Value_Q (Some (Qcdiv q (Qc_of_Z (Z.of_nat (List.length (non_nulls_by isnull l))))))))
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

(** * Mathematical functions of the MySQL family and of SQLite

    The functions call the C library ([Item_func_sqrt], ..., [sql/item_func.cc]; [mathFunc],
    [src/func.c] of SQLite), whose results are correctly rounded ([IEEE.v]). An argument outside the
    domain gives NULL. MySQL raises [ER_DATA_OUT_OF_RANGE] on an infinite or NaN result
    ([check_float_overflow]); SQLite keeps it. [log2] of MySQL is [log (x) / M_LN2] and [log (b, x)]
    [log (x) / log (b)], each [log] rounded; [cot] is [1.0 / tan (x)]; [degrees] and [radians] multiply
    by the double [180 / M_PI] or [M_PI / 180] ([Item_func_units]). For SQLite, [log (x)] is the
    logarithm in base 10, [log (b, x)] is NULL for [b <= 1], and [degrees (x)] is [x * 180.0 / M_PI]. *)
Definition dbl (q : Q) : Q := this (snd (round_q binary64 q)).

Definition c_math_table (lite : bool) (conv : value -> option num) : list (string * (list value -> value)) :=
  let null := Value_F None in
  let range (v : value) :=
      if lite then match v with
                   (* a NaN is stored as NULL ([sqlite3VdbeMemSetDouble]) *)
                   | Value_F (Some (_, k)) => if Nat.eqb (Nat.div (Nat.modulo k 10) 2) 4 then Value_F None else v
                   | _ => v end
      else match v with
           | Value_F (Some (_, k)) => match special_of_tag (Nat.div (Nat.modulo k 10) 2) with
                                      | F_PosInf | F_NegInf | F_NaN => Value_Err "DOUBLE value is out of range"
                                      | _ => v end
           | _ => v end in
  let f1 (f : Q -> option (fspecial * Qc)) l := range (dbl_fun1 conv f null (fun s => VF false (s, Qc_of_Z 0)) null l) in
  let f2 (f : Q -> Q -> option (fspecial * Qc)) l := range (dbl_fun2 conv f null null l) in
  let pos (f : Q -> fspecial * Qc) q := if Z.leb (Qnum q) 0 then None else Some (f q) in
  let ln1 := pos (fun q => round_q binary64 (ln_exact q)) in
  let log10 := pos (fun q => round_q binary64 (Qdiv (ln_exact q) (ln_exact 10))) in
  (* SQLite: [log (b)] must be positive *)
  let log_b (b x : Q) := if Z.leb (Qnum b) 0 || Qeq_bool b 1 || Z.leb (Qnum x) 0 then None
                         else if lite && Qle_bool b 1 then None
                         else Some (round_q binary64 (Qdiv (dbl (ln_exact x)) (dbl (ln_exact b)))) in
  let log2 := if lite then pos (fun q => round_q binary64 (Qdiv (ln_exact q) (ln_exact 2)))
              else pos (fun q => round_q binary64 (Qdiv (dbl (ln_exact q)) (dbl (ln_exact 2)))) in
  let pow := f2 (fun x y => match pow_c x y with
                            | Some r => Some r
                            (* [pow] of the C library returns NaN *)
                            | None => if Z.eqb (Qnum x) 0 then Some (F_PosInf, Qc_of_Z 0) else Some (F_NaN, Qc_of_Z 0) end) in
  let atan_any l := match l with
                    | _ :: nil => f1 (fun q => Some (atan_q binary64 q)) l
                    | _ => f2 (fun y x => Some (atan2_q binary64 y x)) l end in
     ("sqrt", f1 (fun q => if Z.ltb (Qnum q) 0 then None else Some (sqrt_q binary64 q)))
  :: ("exp", f1 (fun q => Some (exp_q binary64 q)))
  :: ("ln", f1 ln1)
  :: ("log", fun l => match l with
                      | _ :: nil => f1 (if lite then log10 else ln1) l
                      | _ => f2 log_b l end)
  :: ("log2", f1 log2)
  :: ("log10", f1 log10)
  :: ("sin", f1 (fun q => Some (sin_q binary64 q)))
  :: ("cos", f1 (fun q => Some (cos_q binary64 q)))
  :: ("tan", f1 (fun q => Some (tan_q binary64 q)))
  :: ("cot", f1 (fun q => let t := snd (tan_q binary64 q) in
                          if Qc_is_zero t then Some (F_PosInf, Qc_of_Z 0) else Some (round_q binary64 (Qinv (this t)))))
  :: ("asin", f1 (asin_q binary64)) :: ("acos", f1 (acos_q binary64))
  :: ("atan", atan_any) :: ("atan2", f2 (fun y x => Some (atan2_q binary64 y x)))
  :: ("sinh", f1 (fun q => Some (hyp_q binary64 0 q)))
  :: ("cosh", f1 (fun q => Some (hyp_q binary64 1 q)))
  :: ("tanh", f1 (fun q => Some (hyp_q binary64 2 q)))
  :: ("degrees", f1 (fun q => Some (if lite then degrees_c q else degrees_my q)))
  :: ("radians", f1 (fun q => Some (if lite then radians_c q else radians_my q)))
  (* [PI()] of MySQL has 6 decimals ([Item_func_pi]) *)
  :: ("pi", fun l => match l with
                     | nil => if lite then VF false (F_Finite, pi_double) else with_fdec (Some 6%nat) (VF false (F_Finite, pi_double))
                     | _ => null end)
  :: ("power", pow) :: ("pow", pow)
  :: nil.

(** * Bits and integers of the MySQL family and of SQLite

    MySQL: [&], [|], [^], [~], [<<], [>>] and [BIT_COUNT] work on [BIGINT UNSIGNED] (64 bits): a negative
    argument is taken modulo [2^64], a shift by 64 or more gives 0 ([Item_func_bit], [sql/item_func.cc]);
    a non-integer argument is rounded. SQLite: the operators work on signed 64-bit integers, a [REAL]
    argument is truncated; a negative shift shifts the other way, a shift by 64 or more gives 0 (or -1 for
    [>>] of a negative number) ([sqlite3VdbeExec], [OP_ShiftLeft]). *)
Definition u64 (z : Z) : Z := Z.modulo z (2 ^ 64).
Definition s64 (z : Z) : Z := let u := u64 z in if 2 ^ 63 <=? u then u - 2 ^ 64 else u.

Fixpoint popcount_pos (p : positive) : Z :=
  match p with xH => 1 | xO q => popcount_pos q | xI q => 1 + popcount_pos q end.
Definition popcount (z : Z) : Z := match z with Zpos p => popcount_pos p | _ => 0 end.

(** the integer of an argument: rounded (MySQL) or truncated (SQLite) *)
Definition int_arg (trunc : bool) (conv : value -> option num) (v : value) : option Z :=
  match conv v with
  | Some (Num_Z z) => Some z
  | Some (Num_Q q) => Some (if trunc then Qc_trunc q else Qc_round q)
  | None => None
  end.

Definition bit_fun (lite : bool) (conv : value -> option num) (f : list Z -> option Z) (l : list value) : value :=
  if existsb is_null l then (if lite then Value_Z None else Value_I None)
  else match fold_right (fun v acc => match int_arg lite conv v, acc with Some z, Some r => Some (z :: r) | _, _ => None end)
                        (Some nil) l with
       | Some zs => match f zs with
                    | Some r => if lite then Value_Z (Some (s64 r)) else Value_I (Some (u64 r, 1%nat))
                    | None => Value_Err "function does not exist"
                    end
       | None => if lite then Value_Z None else Value_I (Some (0, 1%nat))
       end.

Definition bit_table (lite : bool) (conv : value -> option num) : list (string * (list value -> value)) :=
  let b2 (f : Z -> Z -> Z) := bit_fun lite conv (fun l => match l with a :: b :: nil => Some (f a b) | _ => None end) in
  let norm z := if lite then s64 z else u64 z in
  let shift (left : bool) (a n : Z) :=
      let a := norm a in
      if lite then
        let (left, n) := if n <? 0 then (negb left, - n) else (left, n) in
        if 64 <=? n then (if left then 0 else if a <? 0 then -1 else 0)
        else if left then Z.shiftl a n else Z.shiftr a n
      else
        let n := u64 n in
        if 64 <=? n then 0 else if left then Z.shiftl a n else Z.shiftr a n in
     ("&", b2 (fun a b => Z.land (norm a) (norm b)))
  :: ("|", b2 (fun a b => Z.lor (norm a) (norm b)))
  :: ("^", b2 (fun a b => Z.lxor (norm a) (norm b)))
  :: ("~", bit_fun lite conv (fun l => match l with a :: nil => Some (Z.lnot (norm a)) | _ => None end))
  :: ("<<", b2 (shift true)) :: (">>", b2 (shift false))
  :: ("bit_count", fun l => match bit_fun false conv (fun l => match l with a :: nil => Some a | _ => None end) l with
                            | Value_I (Some (z, _)) => Value_Z (Some (popcount z))
                            | Value_I None => Value_Z None
                            | v => v end)
  :: nil.

(** [RAND(N)] of the MySQL family: the first number of the generator seeded with [N] ([my_rnd_init],
    [my_rnd], [mysys/my_rnd.c]). The value is the one of the first row: the generator advances at each
    row, which the model, whose functions have no state, does not follow. [RAND()] without seed is not
    deterministic and is not modelled (an error). *)
Definition my_rand_seeded (n : Z) : value :=
  let m := 1073741823 in
  let t := Z.modulo n (2 ^ 32) in
  let s1 := Z.modulo (Z.modulo (t * 65537 + 55555555) (2 ^ 32)) m in
  let s2 := Z.modulo (Z.modulo (t * 268435457) (2 ^ 32)) m in
  let s1' := Z.modulo (s1 * 3 + s2) m in
  VF false (round_q binary64 (Qmake s1' (Z.to_pos m))).

Definition my_rand (conv : value -> option num) (l : list value) : value :=
  match l with
  | v :: nil => if is_null v then my_rand_seeded 0 else match int_arg false conv v with Some n => my_rand_seeded n | None => my_rand_seeded 0 end
  | _ => Value_Err "nondeterministic function"
  end.

(** [ceil], [ceiling], [floor] and [trunc] of SQLite: an integer is kept, a [REAL] gives a [REAL]
    ([ceilingFunc], [src/func.c]) *)
Definition lite_round_table (conv : value -> option num) : list (string * (list value -> value)) :=
  let f (g : Qc -> Z) (l : list value) :=
      match l with
      | v :: nil =>
        if is_null v then Value_Z None
        else match v with
             | Value_F (Some (x, k)) => if Nat.eqb (Nat.div (Nat.modulo k 10) 2) 0
                                        then VF false (F_Finite, Qc_of_Z (g x)) else v
             | _ => match conv v with
                    | Some (Num_Z z) => Value_Z (Some z)
                    | Some (Num_Q q) => VF false (F_Finite, Qc_of_Z (g q))
                    | None => Value_Z None
                    end
             end
      | _ => Value_Err "wrong number of arguments"
      end in
     ("ceil", f Qc_ceiling) :: ("ceiling", f Qc_ceiling) :: ("floor", f Qc_floor) :: ("trunc", f Qc_trunc)
  :: ("random", fun _ => Value_Err "nondeterministic function")
  :: nil.

(** The key of a value for [GROUP BY], [DISTINCT] and the set operations, shared by the dialects whose numbers
    are identified by their value (an integer, a decimal of any scale and a finite double which are equal are
    not distinct) *)
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

(** The truth of a value and the value of a truth in the dialects whose conditions are integers (the MySQL
    family, SQLite): a non-zero number is true, 0 is false, a value which is not a number is UNKNOWN *)
Definition my_truth (v : value) : bool3 :=
  match lenient v with 
  | Some n => bool3_of_bool (negb (num_is_zero n)) 
  | None => unknown3 
  end.

Definition my_of_truth (b : bool3) : value :=
  match b with true3 => Value_Z (Some 1) | false3 => Value_Z (Some 0) | unknown3 => Value_Z None end.

(** Helpers shared by the MySQL family and SQLite (moved from [MySQL.v], TODO 6.7) *)
Definition truth_is (t : bool3) (v : value) : bool3 :=
  bool3_of_bool (match my_truth v, t with
                 | true3, true3 | false3, false3 | unknown3, unknown3 => true
                 | _, _ => false
                 end).

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
