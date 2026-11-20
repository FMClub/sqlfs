(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Aggregates (TODO 2.5): variance and standard deviation with the result types  *)
(**   of each dialect, the statistics of two variables, [bit_xor], [any_value],     *)
(**   the JSON aggregates, [count (distinct a, b)].                                 *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String ZArith QArith Qcanon Bool.

Require Import IEEE Json Values ValueKit.

Import ListNotations.
Import NullValues.
Open Scope Z_scope.
Open Scope bool_scope.

(** the pairs of an aggregate of two arguments: the evaluation gives [e1; s1; e2; s2; ...] ([E_AggX]) *)
Fixpoint pairs_of (l : list value) : list (value * value) :=
  match l with a :: b :: r => (a, b) :: pairs_of r | _ => nil end.

Definition qc_of (conv : value -> option num) (v : value) : option Qc :=
  match v with
  | Value_F (Some (x, k)) => if Nat.leb (Nat.div (Nat.modulo k 10) 2) 1 then Some x else None
  | _ => match conv v with Some n => Some (Qc_of_num n) | None => None end
  end.

Definition qcs (isnull : value -> bool) (conv : value -> option num) (l : list value) : list Qc :=
  flat_map (fun v => if isnull v then nil else match qc_of conv v with Some q => [q] | None => nil end) l.

Definition qsum (l : list Qc) : Qc := fold_left Qcplus l (Qc_of_Z 0).
Definition qlen (l : list Qc) : Qc := Qc_of_Z (Z.of_nat (List.length l)).

(** [N * sum x^2 - (sum x)^2] and the denominator [N * N] (population) or [N * (N - 1)] (sample) *)
Definition var_frac (sample : bool) (l : list Qc) : option (Qc * Qc) :=
  match l with
  | nil => None
  | _ => let n := qlen l in
         let s := qsum l in
         let s2 := qsum (map (fun x => Qcmult x x) l) in
         let num := Qcminus (Qcmult n s2) (Qcmult s s) in
         let den := Qcmult n (if sample then Qcminus n (Qc_of_Z 1) else n) in
         if Qc_is_zero den then None else Some (num, den)
  end.

(** a double from an exact value, possibly its square root (correctly rounded) *)
Definition dbl_of (root : bool) (q : Qc) : value :=
  if root then VF false (sqrt_q binary64 (this q)) else to_float false q.

(** MySQL: the variance and the standard deviation are [DOUBLE] ([Item_sum_variance]); a sample of one row
    gives NULL *)
Definition my_var_agg (sample root : bool) (isnull : value -> bool) (conv : value -> option num) (l : list value) : value :=
  match var_frac sample (qcs isnull conv l) with
  | Some (num, den) => dbl_of root (Qcdiv num den)
  | None => Value_F None
  end.

(** PostgreSQL ([numeric_stddev_internal]): of integers or [numeric] values, a [numeric] whose scale is
    [select_div_scale] of [N * sum x^2 - (sum x)^2] (scale twice the one of the values) by the
    denominator; of doubles, a double *)
Definition pg_var_agg (sample root : bool) (l : list value) : value :=
  let nn := filter (fun v => negb (is_null v)) l in
  if existsb is_F nn then
    match var_frac sample (qcs is_null num_of_value nn) with
    | Some (num, den) => dbl_of root (Qcdiv num den)
    | None => Value_F None
    end
  (* one value: the population variance is the constant zero ([make_result (&const_zero)], scale 0) *)
  else if Nat.eqb (List.length nn) 1 && negb sample then VDec (Qc_of_Z 0) 0 0
  else
    let sc := fold_left (fun acc v => match dec_of_value v with Some (_, _, s) => Nat.max acc s | None => acc end) nn 0%nat in
    match var_frac sample (qcs is_null num_of_value nn) with
    | Some (num, den) =>
      let r := pg_div_scale num (2 * sc) den 0 in
      let v := Qcdiv num den in
      if root then
        (* the square root, rounded to [r] decimals *)
        let n := Qnum v in let d := Zpos (Qden v) in
        let mq := isqrt ((n * pow10 (2 * r + 2)) / d) in
        VDec (Qcdiv (Qc_of_Z ((mq + 5) / 10)) (Qc_pow10 r)) r r
      else VDec (dec_round v r) r r
    | None => Value_D None
    end.

(** ** The statistics of two variables (PostgreSQL [float8_regr_*], Oracle): the pairs [(y, x)] where both are
    not NULL; the results are doubles, computed exactly and rounded once *)
Definition stat2 (isnull : value -> bool) (conv : value -> option num) (l : list value) : list (Qc * Qc) :=
  flat_map (fun p => match p with
                     | (y, x) => if isnull y || isnull x then nil
                                 else match qc_of conv y, qc_of conv x with Some a, Some b => [(a, b)] | _, _ => nil end
                     end) (pairs_of l).

Definition sxx (l : list (Qc * Qc)) (f g : Qc * Qc -> Qc) : Qc :=
  let n := qlen (map fst l) in
  Qcminus (Qcmult n (qsum (map (fun p => Qcmult (f p) (g p)) l))) (Qcmult (qsum (map f l)) (qsum (map g l))).

(** [which]: covar_pop, covar_samp, corr, regr_slope, regr_intercept, regr_r2, regr_sxx, regr_syy, regr_sxy,
    regr_avgx, regr_avgy; [regr_count] is an integer *)
Definition stat2_agg (which : string) (isnull : value -> bool) (conv : value -> option num) (l : list value) : value :=
  let ps := stat2 isnull conv l in
  let n := qlen (map fst ps) in
  let y := fst in let x := snd in
  let fx := Value_F None in
  let ret (q : Qc) := to_float false q in
  if String.eqb which "regr_count" then Value_Z (Some (Z.of_nat (List.length ps)))
  else match ps with
  | nil => fx
  | _ =>
    let syy := sxx ps y y in let sxx' := sxx ps x x in let sxy := sxx ps x y in
    match which with
    | "covar_pop" => ret (Qcdiv sxy (Qcmult n n))
    | "covar_samp" => if Nat.leb (List.length ps) 1 then fx else ret (Qcdiv sxy (Qcmult n (Qcminus n (Qc_of_Z 1))))
    | "corr" => if Qc_is_zero sxx' || Qc_is_zero syy then fx
                else (* the sign of [sxy] times the square root of [sxy^2 / (sxx syy)] *)
                     let r := snd (sqrt_q binary64 (this (Qcdiv (Qcmult sxy sxy) (Qcmult sxx' syy)))) in
                     VF false (F_Finite, if Qc_lt_bool sxy (Qc_of_Z 0) then Qcopp r else r)
    | "regr_slope" => if Qc_is_zero sxx' then fx else ret (Qcdiv sxy sxx')
    | "regr_intercept" => if Qc_is_zero sxx' then fx
                          else ret (Qcdiv (Qcminus (Qcmult (qsum (map y ps)) sxx') (Qcmult (qsum (map x ps)) sxy)) (Qcmult n sxx'))
    | "regr_r2" => if Qc_is_zero sxx' then fx else if Qc_is_zero syy then ret (Qc_of_Z 1)
                   else ret (Qcdiv (Qcmult sxy sxy) (Qcmult sxx' syy))
    | "regr_sxx" => ret (Qcdiv sxx' n)
    | "regr_syy" => ret (Qcdiv syy n)
    | "regr_sxy" => ret (Qcdiv sxy n)
    | "regr_avgx" => ret (Qcdiv (qsum (map x ps)) n)
    | "regr_avgy" => ret (Qcdiv (qsum (map y ps)) n)
    | _ => Value_Err "function does not exist"
    end
  end%string.

(** [count (distinct a, b)] (MySQL): the distinct pairs without NULL *)
Definition count_distinct2 (isnull : value -> bool) (eq : value -> value -> bool) (l : list value) : value :=
  let ps := filter (fun p => negb (isnull (fst p) || isnull (snd p))) (pairs_of l) in
  let fix dedup (acc : list (value * value)) (r : list (value * value)) :=
      match r with
      | nil => List.length acc
      | p :: r' => if existsb (fun q => eq (fst p) (fst q) && eq (snd p) (snd q)) acc then dedup acc r' else dedup (p :: acc) r'
      end in
  Value_Z (Some (Z.of_nat (dedup nil ps))).

(** [bit_xor]: MySQL gives 0 on the empty group and an unsigned result; PostgreSQL NULL *)
Definition bit_xor_agg (mysql : bool) (isnull : value -> bool) (conv : value -> option num) (l : list value) : value :=
  let zs := flat_map (fun v => if isnull v then nil else match conv v with
                                                         | Some (Num_Z z) => [z] | Some (Num_Q q) => [Qc_round q] | None => nil end) l in
  if mysql then Value_I (Some (fold_left (fun a z => Z.lxor a (Z.modulo z (2 ^ 64))) zs 0, 1%nat))
  else match zs with nil => Value_Z None | z :: r => Value_Z (Some (fold_left Z.lxor r z)) end.

(** [any_value] (PostgreSQL 16): the result is any non-NULL value of the group; the model takes the first
    (one of the possible results) *)
Definition any_value_agg (isnull : value -> bool) (l : list value) : value :=
  match filter (fun v => negb (isnull v)) l with v :: _ => v | nil => match l with v :: _ => v | nil => Value_Z None end end.

(** ** JSON aggregates: MySQL [JSON_ARRAYAGG] and [JSON_OBJECTAGG] (a [JSON] document; a NULL value is
    [null]; a NULL key is an error), PostgreSQL [json_agg] (the text ["[a, b]"]), [jsonb_agg],
    [json_object_agg] (["{ "k" : v, ... }"]), [jsonb_object_agg]; NULL on the empty group *)
Definition json_array_agg (kind : nat) (conv : value -> json) (l : list value) : value :=
  match l with
  | nil => Value_J None
  | _ => if Nat.eqb kind 1
         then Value_J (Some (("[" ++ String.concat ", " (map (fun v => text_compact (conv v)) l) ++ "]")%string, 1%nat))
         else VJ 0 (JArr (map conv l))
  end.

Definition json_object_agg (kind : nat) (isnull : value -> bool) (key : value -> option string) (conv : value -> json) (l : list value) : value :=
  let ps := pairs_of l in
  match ps with
  | nil => Value_J None
  | _ =>
    if existsb (fun p => isnull (fst p)) ps then Value_Err "JSON documents may not contain NULL member names"
    else
      let members := flat_map (fun p => match key (fst p) with Some k => [(k, conv (snd p))] | None => nil end) ps in
      if Nat.eqb kind 1
      then Value_J (Some (("{ " ++ String.concat ", " (map (fun m => text_compact (JStr (fst m)) ++ " : " ++ text_compact (snd m)) members) ++ " }")%string, 1%nat))
      else VJ 0 (JObj members)
  end.

(** * Ordered-set and hypothetical-set aggregates (TODO 2.6)

    [percentile_cont (f) WITHIN GROUP (ORDER BY x)] is [E_AggX] with [x], the direct argument [f] in the
    place of the separator, and the [ORDER BY]: the aggregate receives [x1; f; x2; f; ...] in the order of
    the group. *)
Definition sorted_args (isnull : value -> bool) (l : list value) : option value * list value :=
  match pairs_of l with
  | nil => (None, nil)
  | (_, f) :: _ => (Some f, filter (fun v => negb (isnull v)) (map fst (pairs_of l)))
  end.

(** [percentile_cont]: the value at the position [1 + f (n - 1)], interpolated between its neighbours;
    PostgreSQL computes in [double precision], each operation rounded ([percentile_cont_float8_final]);
    [exact] (Oracle) keeps the exact value *)
Definition percentile_cont_agg (exact : bool) (isnull : value -> bool) (conv : value -> option num) (l : list value) : value :=
  match sorted_args isnull l with
  | (Some f, xs) =>
    match qc_of conv f with
    | Some fq =>
      if Qc_lt_bool fq (Qc_of_Z 0) || Qc_lt_bool (Qc_of_Z 1) fq then Value_Err "percentile value is not between 0 and 1"
      else let qs := flat_map (fun v => match qc_of conv v with Some q => [q] | None => nil end) xs in
           match qs with
           | nil => if exact then Value_Q None else Value_F None
           | _ =>
             let n := List.length qs in
             let r64 (q : Qc) : Qc := snd (round_q binary64 (this q)) in
             let pos := if exact then Qcmult fq (Qc_of_Z (Z.of_nat (n - 1))) else r64 (Qcmult fq (Qc_of_Z (Z.of_nat (n - 1)))) in
             let lo := Qc_floor pos in
             let hi := Qc_ceiling pos in
             let a := nth (Z.to_nat lo) qs (Qc_of_Z 0) in
             let b := nth (Z.to_nat hi) qs (Qc_of_Z 0) in
             if exact then Value_Q (Some (Qcplus a (Qcmult (Qcminus b a) (Qcminus pos (Qc_of_Z lo)))))
             else let a := r64 a in let b := r64 b in
                  if Z.eqb lo hi then to_float false a
                  else to_float false (Qcplus a (r64 (Qcmult (r64 (Qcminus b a)) (r64 (Qcminus pos (Qc_of_Z lo))))))
           end
    | None => if isnull f then Value_F None else Value_Err "invalid percentile"
    end
  | (None, _) => Value_F None
  end.

(** [percentile_disc]: the first value whose position in the group is at least [f n] *)
Definition percentile_disc_agg (isnull : value -> bool) (conv : value -> option num) (l : list value) : value :=
  match sorted_args isnull l with
  | (Some f, xs) =>
    match qc_of conv f with
    | Some fq =>
      if Qc_lt_bool fq (Qc_of_Z 0) || Qc_lt_bool (Qc_of_Z 1) fq then Value_Err "percentile value is not between 0 and 1"
      else match xs with
           | nil => Value_Z None
           | _ => let k := Z.max 1 (Qc_ceiling (Qcmult fq (Qc_of_Z (Z.of_nat (List.length xs))))) in
                  nth (Z.to_nat (k - 1)) xs (Value_Z None)
           end
    | None => if isnull f then Value_Z None else Value_Err "invalid percentile"
    end
  | (None, _) => Value_Z None
  end.

(** [mode ()]: the most frequent value; of several, the first in the order of the group *)
Definition mode_agg (isnull : value -> bool) (eq : value -> value -> bool) (l : list value) : value :=
  let xs := filter (fun v => negb (isnull v)) l in
  let count v := List.length (filter (eq v) xs) in
  match xs with
  | nil => Value_Z None
  | x :: r => fold_left (fun best v => if Nat.ltb (count best) (count v) then v else best) r x
  end.

(** the hypothetical-set aggregates: the rank that the row [h] would have in the group ordered by [order]
    ([desc]: descending, the NULLs first, as in PostgreSQL's default; ascending, the NULLs last) *)
Definition hyp_agg (which : string) (desc : bool) (isnull : value -> bool) (order : value -> value -> comparison)
           (l : list value) : value :=
  match pairs_of l with
  | nil => if String.eqb which "rank" || String.eqb which "dense_rank" then Value_Z (Some 1)
           else to_float false (if String.eqb which "cume_dist" then Qc_of_Z 1 else Qc_of_Z 0)
  | (_, h) :: _ =>
    let xs := map fst (pairs_of l) in
    let n := List.length xs in
    let before (x : value) : bool :=
        if isnull x then desc && negb (isnull h)
        else if isnull h then negb desc
        else match order x h with Lt => negb desc | Gt => desc | Eq => false end in
    let peer (x : value) : bool :=
        (isnull x && isnull h) || (negb (isnull x) && negb (isnull h) && match order x h with Eq => true | _ => false end) in
    let nb := List.length (filter before xs) in
    let np := List.length (filter peer xs) in
    match which with
    | "rank" => Value_Z (Some (Z.of_nat (S nb)))
    | "dense_rank" =>
      let fix distinct (acc : list value) (r : list value) :=
          match r with
          | nil => List.length acc
          | x :: r' => if existsb (fun y => (isnull x && isnull y) ||
                                            (negb (isnull x) && negb (isnull y) && match order x y with Eq => true | _ => false end)) acc
                       then distinct acc r' else distinct (x :: acc) r'
          end in
      Value_Z (Some (Z.of_nat (S (distinct nil (filter before xs)))))
    | "percent_rank" => if Nat.eqb n 0 then to_float false (Qc_of_Z 0)
                        else to_float false (Qcdiv (Qc_of_Z (Z.of_nat nb)) (Qc_of_Z (Z.of_nat n)))
    | "cume_dist" => to_float false (Qcdiv (Qc_of_Z (Z.of_nat (nb + np + 1))) (Qc_of_Z (Z.of_nat (S n))))
    | _ => Value_Err "function does not exist"
    end
  end%string.

(** the values in the ascending order of [order] (a stable insertion) *)
Fixpoint insert_by (order : value -> value -> comparison) (v : value) (l : list value) : list value :=
  match l with
  | nil => [v]
  | w :: l' => match order v w with Gt => w :: insert_by order v l' | _ => v :: l end
  end.

Definition sort_by (order : value -> value -> comparison) (l : list value) : list value :=
  fold_right (insert_by order) nil l.

Definition ordered_set_table (exact : bool) (isnull : value -> bool) (conv : value -> option num)
           (order : value -> value -> comparison) : list (string * (list value -> value)) :=
  let eq a b := match order a b with Eq => true | _ => false end in
     ("percentile_cont", percentile_cont_agg exact isnull conv)
  :: ("percentile_disc", percentile_disc_agg isnull conv)
  :: ("mode", mode_agg isnull eq)
  (* [MEDIAN (x)] is [PERCENTILE_CONT (0.5) WITHIN GROUP (ORDER BY x)]: the values are sorted first *)
  :: ("median", fun l => percentile_cont_agg exact isnull conv
                           (flat_map (fun v => [v; Value_Q (Some (Qcdiv (Qc_of_Z 1) (Qc_of_Z 2)))])
                                     (sort_by order (filter (fun v => negb (isnull v)) l))))
  :: flat_map (fun w => [(("hyp_" ++ w ++ "_asc")%string, hyp_agg w false isnull order);
                         (("hyp_" ++ w ++ "_desc")%string, hyp_agg w true isnull order)])
              ["rank"; "dense_rank"; "percent_rank"; "cume_dist"]%string.
