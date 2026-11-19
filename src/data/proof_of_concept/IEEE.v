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
