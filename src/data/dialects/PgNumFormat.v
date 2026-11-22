(************************************************************************************)
(**                                                                                 *)
(**                             The SQLFS Library                                   *)
(**                                                                                 *)
(************************************************************************************)

(** PostgreSQL [to_char (number, format)] (TODO 8.12), after [src/backend/utils/adt/formatting.c]:
    the format is parsed into nodes ([parse_format] with [NUM_keywords]), which fill a description
    ([NUMDesc_prepare]); the number is written as a text by the function of its type ([int4_to_char],
    [numeric_to_char], [float8_to_char]); the nodes are then run over this text ([NUM_processor_to_char],
    [NUM_numpart_to_char]). The locale is C: the decimal point is [.], the group separator [,], the
    currency symbol a space. *)

Require Import List String Ascii ZArith NArith QArith Qcanon Bool.
Require Import IEEE Values.
Import ListNotations.
Import NullValues.
Open Scope Z_scope.
Open Scope bool_scope.

(** * The format *)
Inductive nnode : Type :=
  | N9 | N0 | NDec | ND | NComma | NG | NL
  | NRN : bool -> nnode      (** [RN] ([true]), [rn] *)
  | NTH : bool -> nnode      (** [TH] ([true]), [th] *)
  | NMI | NPL | NSG | NS | NPR | NFM | NB | NV | NE
  | NOther                   (** [C], [SP]: no effect *)
  | NChar : ascii -> nnode.

(** the keywords, in the order of [NUM_keywords] *)
Definition num_keywords : list (string * nnode) :=
  [(",", NComma); (".", NDec); ("0", N0); ("9", N9); ("B", NB); ("C", NOther); ("D", ND); ("EEEE", NE);
   ("FM", NFM); ("G", NG); ("L", NL); ("MI", NMI); ("PL", NPL); ("PR", NPR); ("RN", NRN true); ("SG", NSG);
   ("SP", NOther); ("S", NS); ("TH", NTH true); ("V", NV);
   ("b", NB); ("c", NOther); ("d", ND); ("eeee", NE); ("fm", NFM); ("g", NG); ("l", NL); ("mi", NMI);
   ("pl", NPL); ("pr", NPR); ("rn", NRN false); ("sg", NSG); ("sp", NOther); ("s", NS); ("th", NTH false);
   ("v", NV)]%string.

(** [parse_format]: a text between double quotes is copied (a backslash quotes the next character);
    outside them a backslash is special before a double quote only *)
Fixpoint nparse (fuel : nat) (s : string) (quoted : bool) : list nnode :=
  match fuel with
  | O => nil
  | S f =>
    match s with
    | EmptyString => nil
    | String c r =>
      if quoted then
        if Ascii.eqb c """" then nparse f r false
        else match c, r with
             | "\"%char, String c' r' => NChar c' :: nparse f r' true
             | _, _ => NChar c :: nparse f r true
             end
      else if Ascii.eqb c """" then nparse f r true
      else match find (fun k => prefix (fst k) s) num_keywords with
           | Some (k, n) => n :: nparse f (substring (String.length k) (String.length s - String.length k)%nat s) false
           | None => match c, r with
                     | "\"%char, String """"%char r' => NChar """" :: nparse f r' false
                     | _, _ => NChar c :: nparse f r false
                     end
           end
    end
  end.

(** * The description of the format ([NUMDesc]) *)
Inductive nflag : Type :=
  FDec | FZero | FBlank | FFm | FLsign | FBr | FMinus | FPlus | FRoman | FMulti | FEeee.

Definition nflag_eqb (a b : nflag) : bool :=
  match a, b with
  | FDec, FDec | FZero, FZero | FBlank, FBlank | FFm, FFm | FLsign, FLsign | FBr, FBr | FMinus, FMinus
  | FPlus, FPlus | FRoman, FRoman | FMulti, FMulti | FEeee, FEeee => true
  | _, _ => false
  end.

(** [d_lsign]: 0 none, 1 before the number ([NUM_LSIGN_PRE]), 2 after it *)
Record ndesc : Type := mk_ndesc
  { d_pre : nat; d_post : nat; d_multi : nat; d_zstart : nat; d_zend : nat; d_lsign : nat; d_prels : nat;
    d_flags : list nflag }.

Definition has (f : nflag) (d : ndesc) : bool := existsb (nflag_eqb f) (d_flags d).
Definition add (f : nflag) (d : ndesc) : ndesc :=
  mk_ndesc (d_pre d) (d_post d) (d_multi d) (d_zstart d) (d_zend d) (d_lsign d) (d_prels d) (f :: d_flags d).
Definition del (f : nflag) (d : ndesc) : ndesc :=
  mk_ndesc (d_pre d) (d_post d) (d_multi d) (d_zstart d) (d_zend d) (d_lsign d) (d_prels d)
           (filter (fun g => negb (nflag_eqb f g)) (d_flags d)).
Definition w_pre (d : ndesc) (v : nat) := mk_ndesc v (d_post d) (d_multi d) (d_zstart d) (d_zend d) (d_lsign d) (d_prels d) (d_flags d).
Definition w_post (d : ndesc) (v : nat) := mk_ndesc (d_pre d) v (d_multi d) (d_zstart d) (d_zend d) (d_lsign d) (d_prels d) (d_flags d).
Definition w_multi (d : ndesc) (v : nat) := mk_ndesc (d_pre d) (d_post d) v (d_zstart d) (d_zend d) (d_lsign d) (d_prels d) (d_flags d).
Definition w_zstart (d : ndesc) (v : nat) := mk_ndesc (d_pre d) (d_post d) (d_multi d) v (d_zend d) (d_lsign d) (d_prels d) (d_flags d).
Definition w_zend (d : ndesc) (v : nat) := mk_ndesc (d_pre d) (d_post d) (d_multi d) (d_zstart d) v (d_lsign d) (d_prels d) (d_flags d).
Definition w_lsign (d : ndesc) (v p : nat) := mk_ndesc (d_pre d) (d_post d) (d_multi d) (d_zstart d) (d_zend d) v p (d_flags d).

Definition ndesc0 : ndesc := mk_ndesc 0 0 0 0 0 0 0 nil.

(** [NUMDesc_prepare]; [None] is a syntax error of the format *)
Definition nprepare (d : ndesc) (n : nnode) : option ndesc :=
  match n with
  | NChar _ => Some d
  | _ =>
    if has FEeee d && negb (match n with NE => true | _ => false end) then None   (* EEEE must be the last *)
    else
      let r :=
          match n with
          | N9 => if has FBr d then None
                  else if has FMulti d then Some (w_multi d (S (d_multi d)))
                  else if has FDec d then Some (w_post d (S (d_post d)))
                  else Some (w_pre d (S (d_pre d)))
          | N0 => if has FBr d then None
                  else let d1 := if negb (has FZero d) && negb (has FDec d)
                                 then w_zstart (add FZero d) (S (d_pre d)) else d in
                       let d2 := if has FDec d1 then w_post d1 (S (d_post d1)) else w_pre d1 (S (d_pre d1)) in
                       Some (w_zend d2 (d_pre d2 + d_post d2)%nat)
          | NB => Some (if Nat.eqb (d_pre d) 0 && Nat.eqb (d_post d) 0 && negb (has FZero d) then add FBlank d else d)
          | ND | NDec => if has FDec d || has FMulti d then None else Some (add FDec d)
          | NFM => Some (add FFm d)
          | NS => if has FLsign d || has FPlus d || has FMinus d || has FBr d then None
                  else if negb (has FDec d) then Some (add FLsign (w_lsign d 1 (d_pre d)))
                  else if Nat.eqb (d_lsign d) 0 then Some (add FLsign (w_lsign d 2 (d_prels d)))
                  else Some d
          | NMI => if has FLsign d then None else Some (add FMinus d)
          | NPL => if has FLsign d then None else Some (add FPlus d)
          | NSG => if has FLsign d then None else Some (add FPlus (add FMinus d))
          | NPR => if has FLsign d || has FPlus d || has FMinus d then None else Some (add FBr d)
          | NRN _ => if has FRoman d then None else Some (add FRoman d)
          | NV => if has FDec d then None else Some (add FMulti d)
          | NE => if has FEeee d || has FBlank d || has FFm d || has FLsign d || has FBr d || has FMinus d
                     || has FPlus d || has FRoman d || has FMulti d then None
                  else Some (add FEeee d)
          | _ => Some d
          end in
      match r with
      | Some d' => if has FRoman d' && existsb (fun f => negb (nflag_eqb f FRoman || nflag_eqb f FFm)) (d_flags d')
                   then None else Some d'
      | None => None
      end
  end.

Definition ndescribe (l : list nnode) : option ndesc :=
  fold_left (fun acc n => match acc with Some d => nprepare d n | None => None end) l (Some ndesc0).

(** * Running the nodes over the text of the number ([NUM_processor_to_char]) *)
Record nstate : Type := mk_nstate
  { st_out : string; st_ip : nat; st_curr : nat; st_wrote : bool; st_in : bool }.

Definition emit (t : string) (s : nstate) : nstate :=
  mk_nstate (st_out s ++ t) (st_ip s) (st_curr s) (st_wrote s) (st_in s).
Definition wrote (s : nstate) : nstate := mk_nstate (st_out s) (st_ip s) (st_curr s) true (st_in s).
Definition set_in (b : bool) (s : nstate) : nstate := mk_nstate (st_out s) (st_ip s) (st_curr s) (st_wrote s) b.

Definition char_is (o : option ascii) (c : ascii) : bool :=
  match o with Some x => Ascii.eqb x c | None => false end.

(** [get_last_relevant_decnum]: the position of the last digit after the point which is not a zero, or
    of the point *)
Definition last_relevant (t : string) : option nat :=
  match index 0 "." t with
  | Some p => Some (fold_left (fun acc i => if char_is (get i t) "0" then acc else i)
                              (seq (S p) (String.length t - S p)%nat) p)
  | None => None
  end.

Section Proc.
Variable d : ndesc.            (* after the adjustments of the start of [NUM_processor_to_char] *)
Variable input : string.
Variable neg : bool.           (* the sign is [-] *)
Variable ops : nat.            (* [out_pre_spaces] *)
Variable lr : option nat.      (* [last_relevant] *)
Variable ncount : Z.           (* [num_count] *)

Let fm := has FFm d.
Let zero := has FZero d.
Let sign_text : string := if neg then "-" else "+".
Let lr_dot : bool := match lr with Some p => char_is (get p input) "." | None => false end.

(** [NUM_numpart_to_char] for [9], [0], [.] and [D] *)
Definition numpart (is0 : bool) (s : nstate) : nstate :=
  if has FRoman d then s else
  let curr := st_curr s in
  let s := set_in false s in
  let predec := negb zero && Nat.eqb (st_ip s) 0 && char_is (get 0 input) "0" && negb (Nat.eqb (d_post d) 0) in
  (* the sign *)
  let s :=
      if negb (st_wrote s) && (Nat.leb ops curr || (zero && Nat.eqb (d_zstart d) curr)) && (negb predec || lr_dot)
      then if has FLsign d then (if Nat.eqb (d_lsign d) 1 then wrote (emit sign_text s) else s)
           else if has FBr d then wrote (emit (if neg then "<" else " ") s)
           else if neg then wrote (emit "-" s)
           else wrote (if fm then s else emit " " s)
      else s in
  (* the digit, the zero, the space or the point *)
  let s :=
      if Nat.ltb curr ops && (Nat.ltb curr (d_zstart d) || negb zero) then (if fm then s else emit " " s)
      else if zero && Nat.ltb curr ops && Nat.leb (d_zstart d) curr then set_in true (emit "0" s)
      else
        let c := get (st_ip s) input in
        let s' :=
            if char_is c "." then emit "." s
            else if match lr with Some p => Nat.ltb p (st_ip s) | None => false end && negb is0 then s
            else if predec then (if negb fm then emit " " s else if lr_dot then emit "0" s else s)
            else match c with Some ch => set_in true (emit (String ch EmptyString) s) | None => s end in
        match c with
        | Some _ => mk_nstate (st_out s') (S (st_ip s')) (st_curr s') (st_wrote s') (st_in s')
        | None => s'
        end in
  let end_ := match lr with
              | Some p => if Nat.eqb p (st_ip s) then Z.of_nat curr
                          else ncount + (if Nat.eqb ops 0 then 0 else 1) + (if has FDec d then 1 else 0)
              | None => ncount + (if Nat.eqb ops 0 then 0 else 1) + (if has FDec d then 1 else 0)
              end in
  let s := if Z.of_nat curr + 1 =? end_
           then if st_wrote s && has FBr d then emit (if neg then ">" else " ") s
                else if has FLsign d && Nat.eqb (d_lsign d) 2 then emit sign_text s
                else s
           else s in
  mk_nstate (st_out s) (st_ip s) (S curr) (st_wrote s) (st_in s).

(** [get_th] *)
Definition th_text (upper : bool) : option string :=
  let n := String.length input in
  match get (n - 1)%nat input with
  | Some c =>
    let k := Z.of_nat (nat_of_ascii c) - 48 in
    if (0 <=? k) && (k <=? 9) then
      let k := if Nat.ltb 1 n && char_is (get (n - 2)%nat input) "1" then 0 else k in
      Some (if k =? 1 then (if upper then "ST"%string else "st"%string)
            else if k =? 2 then (if upper then "ND"%string else "nd"%string)
            else if k =? 3 then (if upper then "RD"%string else "rd"%string)
            else (if upper then "TH"%string else "th"%string))
    else None
  | None => None
  end.

Definition lower_ascii (c : ascii) : ascii :=
  let n := nat_of_ascii c in if Nat.leb 65 n && Nat.leb n 90 then ascii_of_nat (n + 32)%nat else c.
Fixpoint lower_text (t : string) : string :=
  match t with String c r => String (lower_ascii c) (lower_text r) | EmptyString => EmptyString end.

(** a node; [None]: an error ([get_th] on a text which does not end with a digit) *)
Definition nstep (s : nstate) (n : nnode) : option nstate :=
  match n with
  | N9 | NDec | ND => Some (numpart false s)
  | N0 => Some (numpart true s)
  | NComma | NG => Some (if st_in s then emit "," s else if fm then s else emit " " s)
  | NL => Some (emit " " s)
  | NRN upper =>
    let t := substring (st_ip s) (String.length input - st_ip s)%nat input in
    let t := if upper then t else lower_text t in
    Some (emit (if fm then t else repeat_char (15 - String.length t)%nat " " ++ t) s)
  | NTH upper =>
    if has FRoman d || char_is (get 0 input) "#" || neg || has FDec d then Some s
    else match th_text upper with Some t => Some (emit t s) | None => None end
  | NMI => Some (if neg then emit "-" s else if fm then s else emit " " s)
  | NPL => Some (if negb neg then emit "+" s else if fm then s else emit " " s)
  | NSG => Some (emit sign_text s)
  | NChar c => Some (emit (String c EmptyString) s)
  | _ => Some s
  end.
End Proc.

(** [NUM_processor_to_char]: the text of the number, its sign and the number of leading positions without
    digit are given by the function of the type *)
Definition nprocess (nodes : list nnode) (d : ndesc) (input : string) (neg : bool) (ops : nat) : option string :=
  if has FEeee d then Some input else
  let d := if Nat.eqb (d_zstart d) 0 then d else w_zstart d (d_zstart d - 1)%nat in
  let pm := has FPlus d || has FMinus d in
  let d := if negb pm && negb neg && has FFm d then del FBr d else d in
  let wrote0 := if pm then negb (has FPlus d && negb (has FMinus d))
                else negb neg && has FFm d && negb (has FLsign d) in
  let d := if negb pm && Nat.eqb (d_lsign d) 1 && Nat.eqb (d_pre d) (d_prels d) then w_lsign d 2 (d_prels d) else d in
  let lr := if has FFm d && has FDec d
            then match last_relevant input with
                 | Some p => if Nat.ltb ops (d_zend d)
                             then let lz := Nat.min (String.length input - 1)%nat (d_zend d - ops)%nat in
                                  Some (if Nat.ltb p lz then lz else p)
                             else Some p
                 | None => None
                 end
            else None in
  let ncount := Z.of_nat (d_post d) + Z.of_nat (d_pre d) - 1 + (if negb wrote0 && Nat.eqb ops 0 then 1 else 0) in
  match fold_left (fun acc n => match acc with Some s => nstep d input neg ops lr ncount s n | None => None end)
                  nodes (Some (mk_nstate "" 0 0 wrote0 false)) with
  | Some s => Some (st_out s)
  | None => None
  end.

(** * The text of the number *)

(** [int_to_roman] *)
Definition roman (n : Z) : string :=
  if (n <? 1) || (3999 <? n) then repeat_char 15 "#"
  else
    let pick (l : list string) (k : Z) := nth (Z.to_nat k) l ""%string in
    (pick [""; "M"; "MM"; "MMM"] (n / 1000) ++
     pick [""; "C"; "CC"; "CCC"; "CD"; "D"; "DC"; "DCC"; "DCCC"; "CM"] (n / 100 mod 10) ++
     pick [""; "X"; "XX"; "XXX"; "XL"; "L"; "LX"; "LXX"; "LXXX"; "XC"] (n / 10 mod 10) ++
     pick [""; "I"; "II"; "III"; "IV"; "V"; "VI"; "VII"; "VIII"; "IX"] (n mod 10))%string.

(** the digits [m] of a mantissa with [p] decimals and the exponent: [d.ddde+XX] *)
Definition sci_text (m : Z) (p : nat) (e : Z) : string :=
  let ds := if m =? 0 then repeat_char (S p) "0" else string_of_Z m in
  (substring 0 1 ds ++ (if Nat.eqb p 0 then "" else "." ++ substring 1 p ds) ++ "e" ++ exp_text 2 true e)%string.

(** [numeric_out_sci]: [p] decimals, rounded half away from zero; without sign *)
Definition numeric_sci (q : Qc) (p : nat) : string :=
  let n := Z.abs (Qnum q) in
  let dn := Zpos (Qden q) in
  if n =? 0 then sci_text 0 p 0
  else
    let e := log10_q n dn in
    let scaled := Qcmult (Qcmult (Q2Qc (Qmake n (Qden q)))
                                 (if e >=? 0 then Q2Qc (Qmake 1 (Z.to_pos (10 ^ e))) else Qc_of_Z (10 ^ (- e))))
                         (Qc_of_Z (10 ^ Z.of_nat p)) in
    let m := Qc_round scaled in
    if m =? 10 ^ (Z.of_nat p + 1) then sci_text (m / 10) p (e + 1) else sci_text m p e.

(** C [%.*e] of a double: [p] decimals, ties to even; without sign *)
Definition float_sci (x : Qc) (p : nat) : string :=
  let n := Z.abs (Qnum x) in
  if n =? 0 then sci_text 0 p 0
  else let (dd, e) := digits_round n (Zpos (Qden x)) (S p) in sci_text dd p (e + Z.of_nat p).

(** C [%.*f] of the absolute value of a double: [p] decimals, ties to even *)
Definition float_fixed (x : Qc) (p : nat) : string :=
  let z := round_half_even (Z.abs (Qnum x) * 10 ^ Z.of_nat p) (Zpos (Qden x)) in
  let m := 10 ^ Z.of_nat p in
  let fp := string_of_Z (z mod m) in
  (string_of_Z (z / m) ++ (if Nat.eqb p 0 then "" else "." ++ repeat_char (p - String.length fp)%nat "0" ++ fp))%string.

(** the text of the digits before the point, for the common end of the three functions: the padding, or
    the [#] of a number which has more digits than the format *)
Definition fit (d : ndesc) (numstr : string) : string * nat :=
  let prelen := match index 0 "." numstr with Some p => p | None => String.length numstr end in
  if Nat.ltb prelen (d_pre d) then (numstr, (d_pre d - prelen)%nat)
  else if Nat.ltb (d_pre d) prelen
       then ((repeat_char (d_pre d) "#" ++ "." ++ repeat_char (d_post d) "#")%string, 0%nat)
       else (numstr, 0%nat).

(** [#] for a number without scientific notation: a space, the [#] of the digits and the point *)
Definition eeee_special (d : ndesc) : string :=
  (" " ++ repeat_char (d_pre d) "#" ++ "." ++ repeat_char (d_post d + 4)%nat "#")%string.

Definition special_text (sp : fspecial) : string :=
  match sp with F_NaN => "NaN" | _ => "Infinity" end.

Definition with_multi (d : ndesc) : ndesc := if has FMulti d then w_pre d (d_pre d + d_multi d)%nat else d.

(** the description, the text, the sign and the leading positions; [None]: [integer out of range] *)
Definition int_text (d : ndesc) (z : Z) (w : nat) : option (ndesc * string * bool * nat) :=
  if has FRoman d then Some (d, roman z, false, 0%nat)
  else if has FEeee d then
    (* [int4]: by a double ([%+.*e]); [int8]: by a [numeric] *)
    let t := if Nat.eqb w 64 then numeric_sci (Qc_of_Z z) (d_post d)
             else float_sci (snd (round_q binary64 (inject_Z z))) (d_post d) in
    Some (d, String.append (if z <? 0 then "-" else " ") t, false, 0%nat)
  else
    let v := if has FMulti d then z * 10 ^ Z.of_nat (d_multi d) else z in
    if negb (int_range_ok (if Nat.eqb w 64 then 64 else 32) v) then None
    else
      let d := with_multi d in
      let ds := string_of_Z (Z.abs v) in
      let numstr := if Nat.eqb (d_post d) 0 then ds else (ds ++ "." ++ repeat_char (d_post d) "0")%string in
      let (t, ops) := fit d numstr in
      Some (d, t, v <? 0, ops).

Definition numeric_text (d : ndesc) (q : Qc) : ndesc * string * bool * nat :=
  if has FRoman d then
    let z := Qc_round q in (d, roman (if int_range_ok 32 z then z else 2147483647), false, 0%nat)
  else if has FEeee d then (d, String.append (if Qnum q <? 0 then "-" else " ") (numeric_sci q (d_post d)), false, 0%nat)
  else
    let v := if has FMulti d then Qcmult q (Qc_of_Z (10 ^ Z.of_nat (d_multi d))) else q in
    let d := with_multi d in
    let x := dec_round v (d_post d) in
    let t := dec_text x (d_post d) in
    let neg := match t with String "-"%char _ => true | _ => false end in
    let numstr := if neg then substring 1 (String.length t - 1)%nat t else t in
    let (t', ops) := fit d numstr in
    (d, t', neg, ops).

(** [float8_to_char], [float4_to_char] ([dig]: [DBL_DIG] 15, [FLT_DIG] 6) *)
Definition float_text (d : ndesc) (sp : fspecial) (x : Qc) (w32 : bool) : ndesc * string * bool * nat :=
  let finite := match sp with F_Finite | F_NegZero => true | _ => false end in
  if has FRoman d then
    let z := round_half_even (Qnum x) (Zpos (Qden x)) in
    (d, roman (if finite && int_range_ok 32 z then z else 2147483647), false, 0%nat)
  else if has FEeee d then
    if finite then (d, String.append (if Qnum x <? 0 then "-" else " ") (float_sci x (d_post d)), false, 0%nat)
    else (d, eeee_special d, false, 0%nat)
  else
    let f := if w32 then binary32 else binary64 in
    let dig := if w32 then 6%nat else 15%nat in
    let v := if has FMulti d && finite then snd (round_q f (Qcmult x (Qc_of_Z (10 ^ Z.of_nat (d_multi d))))) else x in
    let d := with_multi d in
    let len := String.length (if finite then float_fixed v 0 else special_text sp) in
    let d := if Nat.leb dig len then w_post d 0
             else if Nat.ltb dig (len + d_post d)%nat then w_post d (dig - len)%nat else d in
    let numstr := if finite then float_fixed v (d_post d) else special_text sp in
    let neg := if finite then Qnum v <? 0 else match sp with F_NegInf => true | _ => false end in
    let (t, ops) := fit d numstr in
    (d, t, neg, ops).

(** [to_char (v, fmt)] for a number *)
Definition pg_num_to_char (v : value) (fmt : string) : value :=
  if String.eqb fmt "" then Value_string (Some ""%string)
  else
    let nodes := nparse (S (String.length fmt)) fmt false in
    match ndescribe nodes with
    | None => Value_Err "invalid numeric format"
    | Some d =>
      let parts :=
          match v with
          | Value_D (Some (q, _, _)) => Some (numeric_text d q)
          | Value_Q (Some q) => Some (numeric_text d q)
          | _ => match int_parts v, float_parts v with
                 | Some (z, w), _ => int_text d z w
                 | None, Some (sp, x, w32) => Some (float_text d sp x w32)
                 | None, None => None
                 end
          end in
      match parts with
      | Some (d', t, neg, ops) =>
        match nprocess nodes d' t neg ops with
        | Some r => Value_string (Some r)
        | None => Value_Err "is not a number"
        end
      | None => Value_Err "integer out of range"
      end
    end.
