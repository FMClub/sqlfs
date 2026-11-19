(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Binary floating-point numbers (IEEE 754): binary64 ([DOUBLE PRECISION],       *)
(**   [DOUBLE], [REAL] of SQLite) and binary32 ([REAL] of PostgreSQL, [FLOAT] of    *)
(**   MySQL), with rounding to nearest, ties to even, and the texts which the       *)
(**   engines print.                                                                *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String Ascii ZArith QArith Qcanon DecimalString.

Import ListNotations.
Open Scope Z_scope.

(** * Formats

    A format has [prec] bits of precision; its finite numbers are [m * 2^e] with
    [|m| < 2^prec] and [emin <= e <= emax] ([emin] is the exponent of the least subnormal). *)
Record format : Type := mk_format { prec : Z; emin : Z; emax : Z }.

Definition binary64 : format := mk_format 53 (-1074) 971.
Definition binary32 : format := mk_format 24 (-149) 104.

(** * Floating-point values

    The finite values are kept as exact rationals (which are representable in the format); the
    special values are the infinities, NaN and the negative zero. *)
Inductive fspecial : Type := F_Finite | F_NegZero | F_PosInf | F_NegInf | F_NaN.

Definition tag_of (s : fspecial) : nat :=
  match s with F_Finite => 0 | F_NegZero => 1 | F_PosInf => 2 | F_NegInf => 3 | F_NaN => 4 end%nat.

Definition special_of_tag (n : nat) : fspecial :=
  match n with 0 => F_Finite | 1 => F_NegZero | 2 => F_PosInf | 3 => F_NegInf | _ => F_NaN end%nat.

(** * Rounding *)

Definition Qc_of_Z (z : Z) : Qc := Q2Qc (inject_Z z).

(** [floor (log2 (n / d))] for [n, d > 0] *)
Definition log2_q (n d : Z) : Z :=
  let k := Z.log2 n - Z.log2 d in
  (* [2^k <= n/d < 2^(k+2)]: correct by one *)
  if (k >=? 0)
  then (if d * 2 ^ k <=? n then k else k - 1)
  else (if d <=? n * 2 ^ (- k) then k else k - 1).

(** [n / d] rounded to an integer, ties to even, for [n >= 0], [d > 0] *)
Definition round_half_even (n d : Z) : Z :=
  let q := n / d in
  let r := n mod d in
  if 2 * r <? d then q
  else if d <? 2 * r then q + 1
  else if Z.even q then q else q + 1.

(** [a * 2^e] *)
Definition mul_pow2 (a : Q) (e : Z) : Q :=
  if (e >=? 0) then Qmult a (inject_Z (2 ^ e)) else Qdiv a (inject_Z (2 ^ (- e))).

(** The nearest value of the format: a finite value, or an infinity on overflow. *)
Definition round_q (f : format) (q : Q) : fspecial * Qc :=
  let n := Qnum q in
  let d := Zpos (Qden q) in
  if n =? 0 then (F_Finite, Qc_of_Z 0)
  else
    let neg := n <? 0 in
    let a := Z.abs n in
    let k := log2_q a d in
    let e := Z.max (k - (prec f - 1)) (emin f) in
    (* the mantissa: [a / d / 2^e] rounded *)
    let m := if (e >=? 0) then round_half_even a (d * 2 ^ e) else round_half_even (a * 2 ^ (- e)) d in
    let (m, e) := if m =? 2 ^ prec f then (m / 2, e + 1) else (m, e) in
    if emax f <? e then (if neg then F_NegInf else F_PosInf, Qc_of_Z 0)
    else if m =? 0 then (if neg then F_NegZero else F_Finite, Qc_of_Z 0)
    else (F_Finite, Q2Qc (mul_pow2 (inject_Z (if neg then - m else m)) e)).

(** * Texts

    [digits_round x n]: the decimal [D * 10^E] with [n] significant digits nearest to [x > 0]
    (ties to even, as the conversions of the C library), as [(D, E)]. *)
Definition log10_q (n d : Z) : Z :=
  (* [floor (log10 (n/d))] by comparison with powers of 10 *)
  let k := Z.log2 n - Z.log2 d in
  let guess := (k * 30103) / 100000 in
  let ok (e : Z) := (if (e >=? 0) then d * 10 ^ e <=? n else d <=? n * 10 ^ (- e)) in
  let ok' (e : Z) := (if (e + 1 >=? 0) then n <? d * 10 ^ (e + 1) else n * 10 ^ (- (e + 1)) <? d) in
  let cands := map (fun i => guess - 2 + Z.of_nat i) (seq 0 5) in
  match find (fun e => ok e && ok' e) cands with Some e => e | None => guess end.

Definition digits_round (n d : Z) (nd : nat) : Z * Z :=
  let e := log10_q n d - Z.of_nat nd + 1 in
  let dd := if (e >=? 0) then round_half_even n (d * 10 ^ e) else round_half_even (n * 10 ^ (- e)) d in
  if dd =? 10 ^ Z.of_nat nd then (dd / 10, e + 1) else (dd, e).

Definition q_of_digits (dd e : Z) : Q :=
  if (e >=? 0) then inject_Z (dd * 10 ^ e) else Qmake dd (Z.to_pos (10 ^ (- e))).

Definition strip_zeros (dd e : Z) : Z * Z :=
  (* remove the trailing zeros of [dd], at most 20 *)
  fold_left (fun (acc : Z * Z) (_ : nat) => 
               let (x, y) := acc in if (x mod 10 =? 0) && negb (x =? 0) then (x / 10, y + 1) else acc)
            (seq 0 20) (dd, e).

(** the shortest decimal which rounds back to the same value of the format (Ryu, [dtoa] mode 0):
    the digits and the exponent [(D, E)], [x = D * 10^E] *)
Definition shortest (f : format) (x : Qc) : Z * Z :=
  let n := Z.abs (Qnum x) in
  let d := Zpos (Qden x) in
  let cand (k : nat) := digits_round n d k in
  let same k := let (dd, e) := cand k in
                Qc_eq_bool (snd (round_q f (q_of_digits dd e))) (Q2Qc (Qmake n (Qden x))) in
  match find same (seq 1 17) with
  | Some k => strip_zeros (fst (cand k)) (snd (cand k))
  | None => strip_zeros (fst (cand 17%nat)) (snd (cand 17%nat))
  end.

Definition string_of_Z (z : Z) : string := NilZero.string_of_int (Z.to_int z).

Fixpoint repeat_char (n : nat) (c : ascii) : string :=
  match n with O => EmptyString | S n => String c (repeat_char n c) end.

(** The digits [D] (as a text of [len] characters) and the decimal exponent [x = 0.D * 10^decpt] *)
Definition fixed_text (ds : string) (decpt : Z) : string :=
  let len := Z.of_nat (String.length ds) in
  if (decpt <=? 0) then "0." ++ repeat_char (Z.to_nat (- decpt)) "0" ++ ds
  else if (len <=? decpt) then ds ++ repeat_char (Z.to_nat (decpt - len)) "0"
  else substring 0 (Z.to_nat decpt) ds ++ "." ++ substring (Z.to_nat decpt) (Z.to_nat (len - decpt)) ds.

Definition mantissa_text (ds : string) : string :=
  match ds with
  | String c EmptyString => String c EmptyString
  | String c r => String c ("." ++ r)
  | EmptyString => "0"
  end.

Definition exp_text (minwidth : nat) (plus : bool) (x : Z) : string :=
  (if (x <? 0) then "-" else if plus then "+" else "") ++
  let t := string_of_Z (Z.abs x) in repeat_char (minwidth - String.length t) "0" ++ t.

(** PostgreSQL ([float8out], [float4out] with [extra_float_digits] = 1, the default: the shortest text,
    [src/common/d2s.c]): fixed notation when the exponent is in [[-4, 15)], otherwise [d.ddde+XX]. *)
Definition pg_text (f : format) (s : fspecial) (x : Qc) : string :=
  match s with
  | F_NaN => "NaN" | F_PosInf => "Infinity" | F_NegInf => "-Infinity" | F_NegZero => "-0"
  | F_Finite =>
    if Qc_eq_bool x (Qc_of_Z 0) then "0"
    else
      let (dd, e) := shortest f x in
      let ds := string_of_Z dd in
      let exp := e + Z.of_nat (String.length ds) - 1 in
      (if Qnum x <? 0 then "-" else "") ++
      if (-4 <=? exp) && (exp <? 15) then fixed_text ds (exp + 1)
      else mantissa_text ds ++ "e" ++ exp_text 2 true exp
  end.

(** The MySQL family ([my_gcvt] of [strings/dtoa.c], the shortest digits of [dtoa] mode 4 for a wide
    field): fixed notation when [-14 <= decpt <= 15] or when some digit is after the point, where
    [x = 0.D * 10^decpt]; otherwise [D.DDDeX] without a plus sign. *)
Definition my_text (f : format) (s : fspecial) (x : Qc) : string :=
  match s with
  | F_Finite =>
    if Qc_eq_bool x (Qc_of_Z 0) then "0"
    else
      let (dd, e) := shortest f x in
      let ds := string_of_Z dd in
      let len := Z.of_nat (String.length ds) in
      let decpt := e + len in
      (if Qnum x <? 0 then "-" else "") ++
      if (-14 <=? decpt) && ((decpt <=? 15) || (decpt <? len)) then fixed_text ds decpt
      else mantissa_text ds ++ "e" ++ exp_text 0 false (decpt - 1)
  | F_NegZero => "-0"
  | _ => "NULL"
  end.

(** SQLite ([sqlite3_str_vappendf] with ["%!.15g"]): 15 significant digits, trailing zeros removed, at
    least one decimal ([1.0]); exponent form [d.ddde+XX] when the exponent is below -4 or at least 15. *)
Definition lite_text (s : fspecial) (x : Qc) : string :=
  match s with
  | F_PosInf => "Inf" | F_NegInf => "-Inf" | F_NaN => "NULL" | F_NegZero => "-0.0"
  | F_Finite =>
    if Qc_eq_bool x (Qc_of_Z 0) then "0.0"
    else
      let n := Z.abs (Qnum x) in
      let d := Zpos (Qden x) in
      let (dd0, e0) := digits_round n d 15 in
      let (dd, e) := strip_zeros dd0 e0 in
      let ds := string_of_Z dd in
      let exp := e + Z.of_nat (String.length ds) - 1 in
      (if Qnum x <? 0 then "-" else "") ++
      if (-4 <=? exp) && (exp <? 15)
      then let t := fixed_text ds (exp + 1) in
           if (exp + 1 >=? Z.of_nat (String.length ds)) then t ++ ".0" else t
      else (match ds with String c EmptyString => String c ".0" | _ => mantissa_text ds end) ++ "e" ++ exp_text 2 true exp
  end.

(** * Mathematical functions

    The functions of the C library which the engines call ([sqrt], [exp], [log], [sin], ...) return the
    double nearest to the exact result (glibc's are correctly rounded for these functions, except in rare
    cases near a tie, which are not distinguished here). The exact result is computed in fixed point with
    [fp_bits] = 256 fractional bits by the series below, then rounded once. *)
Definition fp_bits : Z := 256.
Definition fp_one : Z := 2 ^ fp_bits.

(** fixed point: a real [x] is [x * 2^256], truncated *)
Definition fp_of_q (q : Q) : Z := (Qnum q * fp_one) / Zpos (Qden q).
Definition q_of_fp (a : Z) : Q := Qmake a (Z.to_pos fp_one).
Definition fp_mul (a b : Z) : Z := (a * b) / fp_one.
Definition fp_div (a b : Z) : Z := (a * fp_one) / b.

(** the integer square root, by Newton's method *)
Fixpoint isqrt_iter (fuel : nat) (n x : Z) : Z :=
  match fuel with
  | O => x
  | S f => let y := (x + n / x) / 2 in if y >=? x then x else isqrt_iter f n y
  end.

Definition isqrt (n : Z) : Z := if n <=? 0 then 0 else isqrt_iter 400 n n.

(** [sqrt q]: correctly rounded (the sticky bit makes the rounding of the truncated root exact) *)
Definition sqrt_q (f : format) (q : Q) : fspecial * Qc :=
  let n := Qnum q in
  let d := Zpos (Qden q) in
  if n <? 0 then (F_NaN, Qc_of_Z 0)
  else if n =? 0 then (F_Finite, Qc_of_Z 0)
  else
    (* sqrt(n/d) = sqrt(n * d) / d; scaled by 2^t *)
    let t := 200 in
    let big := n * d * 2 ^ (2 * t) in
    let r := isqrt big in
    let sticky := negb (r * r =? big) in
    let approx := Qmake (2 * r + (if sticky then 1 else 0)) (Z.to_pos (2 * d * 2 ^ t)) in
    round_q f approx.

(** [ln 2] and the series of [atanh] *)
Fixpoint atanh_series (fuel : nat) (z z2 term : Z) (k : Z) (acc : Z) : Z :=
  match fuel with
  | O => acc
  | S f => if term =? 0 then acc
           else atanh_series f z z2 (fp_mul term z2) (k + 2) (acc + term / k)
  end.

(** [2 atanh z] for [|z| < 1/2] (fixed point) *)
Definition two_atanh (z : Z) : Z := 2 * atanh_series 400 z (fp_mul z z) z 1 0.

Definition fp_ln2 : Z := two_atanh (fp_one / 3).

(** [ln x] for [x > 0]: [x = m 2^k] with [m] in [[1, 2)], [ln m = 2 atanh ((m - 1) / (m + 1))] *)
Definition fp_ln_q (q : Q) : Z :=
  let n := Qnum q in
  let d := Zpos (Qden q) in
  let k := log2_q n d in
  let m := fp_of_q (mul_pow2 q (- k)) in
  two_atanh (fp_div (m - fp_one) (m + fp_one)) + k * fp_ln2.

(** [exp x]: [x = k ln 2 + r], [|r| <= ln 2 / 2], Taylor series of [exp r] *)
Fixpoint exp_series (fuel : nat) (r term : Z) (i : Z) (acc : Z) : Z :=
  match fuel with
  | O => acc
  | S f => if term =? 0 then acc else exp_series f r (fp_mul term r / i) (i + 1) (acc + term)
  end.

Definition exp_q (fm : format) (q : Q) : fspecial * Qc :=
  let x := fp_of_q q in
  let k := (2 * x + fp_ln2) / (2 * fp_ln2) in
  if 2000 <? k then (F_PosInf, Qc_of_Z 0)
  else if k <? -2000 then (F_Finite, Qc_of_Z 0)
  else
    let r := x - k * fp_ln2 in
    let e := exp_series 400 r fp_one 1 0 in
    round_q fm (mul_pow2 (q_of_fp e) k).

(** [ln], [log10], [log2] as doubles; [None] for [x <= 0] (an error or NULL, depending on the engine) *)
Definition ln_q (fm : format) (q : Q) : option (fspecial * Qc) :=
  if Qnum q <=? 0 then None else Some (round_q fm (q_of_fp (fp_ln_q q))).

Definition log_base_q (fm : format) (b : Z) (q : Q) : option (fspecial * Qc) :=
  if Qnum q <=? 0 then None else Some (round_q fm (Qdiv (q_of_fp (fp_ln_q q)) (q_of_fp (fp_ln_q (inject_Z b))))).

(** [pi] (Machin: [pi = 16 atan (1/5) - 4 atan (1/239)]) *)
Fixpoint atan_series (fuel : nat) (z z2 term : Z) (k : Z) (sign : Z) (acc : Z) : Z :=
  match fuel with
  | O => acc
  | S f => if term =? 0 then acc
           else atan_series f z z2 (fp_mul term z2) (k + 2) (- sign) (acc + sign * (term / k))
  end.

Definition fp_atan_small (z : Z) : Z := atan_series 600 z (fp_mul z z) z 1 1 0.

Definition fp_pi : Z := 16 * fp_atan_small (fp_one / 5) - 4 * fp_atan_small (fp_one / 239).

Definition pi_double : Qc := snd (round_q binary64 (q_of_fp fp_pi)).

(** [sin] and [cos]: [x = k pi/2 + r], Taylor series of [sin r] and [cos r] *)
Fixpoint sin_series (fuel : nat) (r2 term : Z) (i : Z) (acc : Z) : Z :=
  match fuel with
  | O => acc
  | S f => if term =? 0 then acc else sin_series f r2 (- (fp_mul term r2) / ((i + 1) * (i + 2))) (i + 2) (acc + term)
  end.

Definition fp_sin_cos (x : Z) : Z * Z :=
  let half_pi := fp_pi / 2 in
  let k := (2 * x + half_pi) / (2 * half_pi) in
  let r := x - k * half_pi in
  let r2 := fp_mul r r in
  let s := sin_series 400 r2 r 1 0 in
  let c := sin_series 400 r2 fp_one 0 0 in
  match k mod 4 with
  | 0 => (s, c) | 1 => (c, - s) | 2 => (- s, - c) | _ => (- c, s)
  end.

Definition sin_q (fm : format) (q : Q) : fspecial * Qc := round_q fm (q_of_fp (fst (fp_sin_cos (fp_of_q q)))).
Definition cos_q (fm : format) (q : Q) : fspecial * Qc := round_q fm (q_of_fp (snd (fp_sin_cos (fp_of_q q)))).
Definition tan_q (fm : format) (q : Q) : fspecial * Qc :=
  let (s, c) := fp_sin_cos (fp_of_q q) in round_q fm (Qdiv (q_of_fp s) (q_of_fp c)).

(** [atan x]: for [|x| > 1/2], [atan x = 2 atan (x / (1 + sqrt (1 + x^2)))] until the series converges fast *)
Fixpoint fp_atan_red (fuel : nat) (x : Z) : Z :=
  match fuel with
  | O => fp_atan_small x
  | S f => if Z.abs x <=? fp_one / 4 then fp_atan_small x
           else 2 * fp_atan_red f (fp_div x (fp_one + isqrt (fp_one * (fp_one + fp_mul x x))))
  end.

Definition atan_q (fm : format) (q : Q) : fspecial * Qc := round_q fm (q_of_fp (fp_atan_red 10 (fp_of_q q))).

(** [asin x = atan (x / sqrt (1 - x^2))], [acos x = pi/2 - asin x]; [None] outside [[-1, 1]] *)
Definition fp_asin (x : Z) : Z :=
  if Z.abs x =? fp_one then (if x >? 0 then fp_pi / 2 else - (fp_pi / 2))
  else fp_atan_red 10 (fp_div x (isqrt (fp_one * (fp_one - fp_mul x x)))).

Definition asin_q (fm : format) (q : Q) : option (fspecial * Qc) :=
  let x := fp_of_q q in if fp_one <? Z.abs x then None else Some (round_q fm (q_of_fp (fp_asin x))).
Definition acos_q (fm : format) (q : Q) : option (fspecial * Qc) :=
  let x := fp_of_q q in if fp_one <? Z.abs x then None else Some (round_q fm (q_of_fp (fp_pi / 2 - fp_asin x))).

(** [atan2 y x] *)
Definition atan2_q (fm : format) (y x : Q) : fspecial * Qc :=
  let fy := fp_of_q y in
  let fx := fp_of_q x in
  let a := if fx =? 0 then (if fy >=? 0 then fp_pi / 2 else - (fp_pi / 2))
           else let base := fp_atan_red 10 (fp_div fy fx) in
                if fx >? 0 then base else if fy >=? 0 then base + fp_pi else base - fp_pi in
  round_q fm (q_of_fp a).

(** [x ^ y] for a non-integer [y] and [x > 0]: [exp (y ln x)] *)
Definition pow_q (fm : format) (x y : Q) : option (fspecial * Qc) :=
  if Qnum x <=? 0 then None
  else let l := fp_ln_q x in
       let e := fp_mul (fp_of_q y) l in
       Some (exp_q fm (q_of_fp e)).

(** [exp x] and [ln x] as rationals (fixed point, 256 bits), for the functions of [numeric]
    and the hyperbolic functions; [None] when [exp x] is out of every range *)
Definition exp_exact (q : Q) : option Q :=
  let x := fp_of_q q in
  let k := (2 * x + fp_ln2) / (2 * fp_ln2) in
  if (5000 <? k) || (k <? -5000) then None
  else let r := x - k * fp_ln2 in Some (mul_pow2 (q_of_fp (exp_series 400 r fp_one 1 0)) k).

Definition ln_exact (q : Q) : Q := q_of_fp (fp_ln_q q).

(** the integer cube root, by Newton's method *)
Fixpoint icbrt_iter (fuel : nat) (n x : Z) : Z :=
  match fuel with
  | O => x
  | S f => let y := (2 * x + n / (x * x)) / 3 in if y >=? x then x else icbrt_iter f n y
  end.

Definition icbrt (n : Z) : Z := if n <=? 0 then 0 else icbrt_iter 2000 n n.

(** [cbrt q]: correctly rounded *)
Definition cbrt_q (f : format) (q : Q) : fspecial * Qc :=
  let n := Qnum q in
  let d := Zpos (Qden q) in
  if n =? 0 then (F_Finite, Qc_of_Z 0)
  else
    let t := 200 in
    let big := Z.abs n * d * d * 2 ^ (3 * t) in
    let r := icbrt big in
    let sticky := negb (r * r * r =? big) in
    let a := Qmake (2 * r + (if sticky then 1 else 0)) (Z.to_pos (2 * d * 2 ^ t)) in
    round_q f (if n <? 0 then Qopp a else a).

(** [sinh], [cosh], [tanh] from [exp] *)
Definition hyp_q (fm : format) (which : nat) (q : Q) : fspecial * Qc :=
  match exp_exact q, exp_exact (Qopp q) with
  | Some a, Some b =>
    round_q fm (match which with
                | O => Qmult (Qminus a b) (1 # 2)
                | 1%nat => Qmult (Qplus a b) (1 # 2)
                | _ => Qdiv (Qminus a b) (Qplus a b)
                end)
  | _, _ => match which with
            | 2%nat => (F_Finite, Qc_of_Z (if Qnum q <? 0 then -1 else 1))
            | 1%nat => (F_PosInf, Qc_of_Z 0)
            | _ => (if Qnum q <? 0 then F_NegInf else F_PosInf, Qc_of_Z 0)
            end
  end.

(** the decimal exponent of a positive rational: [floor (log10 q)] *)
Fixpoint dexp_up (fuel : nat) (n d e : Z) : Z :=
  match fuel with O => e | S f => if d * 10 ^ (e + 1) <=? n then dexp_up f n d (e + 1) else e end.
Fixpoint dexp_down (fuel : nat) (n d e : Z) : Z :=
  match fuel with O => e | S f => if d <=? n * 10 ^ e then - e else dexp_down f n d (e + 1) end.
Definition dexp10 (q : Q) : Z :=
  let n := Z.abs (Qnum q) in
  let d := Zpos (Qden q) in
  if n =? 0 then 0 else if d <=? n then dexp_up 2000 n d 0 else dexp_down 2000 n d 1.
