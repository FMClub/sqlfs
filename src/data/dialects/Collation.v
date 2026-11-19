(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Collations: the comparison of strings of the engines.                         *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String Ascii ZArith Bool.

Require Import CollationData.

Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

(** * UTF-8

    The strings of the model are sequences of bytes; the collations compare code points, which
    are decoded from UTF-8 (an ill-formed byte is taken as the code point of the same value). *)
Definition byte (c : ascii) : Z := Z.of_nat (nat_of_ascii c).

Fixpoint utf8_decode_aux (fuel : nat) (s : string) : list Z :=
  match fuel with
  | O => nil
  | S f =>
    match s with
    | EmptyString => nil
    | String c r =>
      let b := byte c in
      let cont (k : nat) :=
          (* the [k] continuation bytes, if they are there *)
          let bytes := map byte (list_ascii_of_string (substring 0 k r)) in
          if Nat.eqb (List.length bytes) k && forallb (fun x => (128 <=? x) && (x <? 192)) bytes
          then Some (fold_left (fun acc x => acc * 64 + (x - 128)) bytes 0, k)
          else None in
      let one (lead : Z) (k : nat) :=
          match cont k with
          | Some (v, _) => (lead * Z.pow 64 (Z.of_nat k) + v) :: utf8_decode_aux f (substring k (String.length r - k) r)
          | None => b :: utf8_decode_aux f r
          end in
      if b <? 128 then b :: utf8_decode_aux f r
      else if (192 <=? b) && (b <? 224) then one (b - 192) 1%nat
      else if (224 <=? b) && (b <? 240) then one (b - 224) 2%nat
      else if (240 <=? b) && (b <? 248) then one (b - 240) 3%nat
      else b :: utf8_decode_aux f r
    end
  end.

Definition utf8_decode (s : string) : list Z := utf8_decode_aux (String.length s) s.

Definition utf8_encode1 (c : Z) : string :=
  let a (x : Z) := String (ascii_of_nat (Z.to_nat x)) EmptyString in
  if c <? 128 then a c
  else if c <? 2048 then (a (192 + c / 64) ++ a (128 + c mod 64))%string
  else if c <? 65536 then (a (224 + c / 4096) ++ a (128 + (c / 64) mod 64) ++ a (128 + c mod 64))%string
  else (a (240 + c / 262144) ++ a (128 + (c / 4096) mod 64) ++ a (128 + (c / 64) mod 64) ++ a (128 + c mod 64))%string.

Definition utf8_encode (l : list Z) : string := fold_right (fun c acc => (utf8_encode1 c ++ acc)%string) EmptyString l.

(** * Collations *)
Inductive collation : Type :=
  (** the bytes: [C] of PostgreSQL, [BINARY] of SQLite, [utf8mb4_bin], [binary] *)
  | Coll_Binary
  (** [utf8mb4_general_ci]: one weight per character, its upper case without accent (MySQL,
      MariaDB, OceanBase); the supplementary characters weigh as U+FFFD *)
  | Coll_General_CI
  (** [utf8mb4_0900_ai_ci]: the primary weights of UCA 9.0.0 (MySQL 8) *)
  | Coll_UCA900_AI_CI
  (** [utf8mb4_unicode_520_ci]: the primary weights of UCA 5.2.0 *)
  | Coll_UCA520_CI
  (** [utf8mb4_unicode_ci]: the primary weights of UCA 4.0.0 *)
  | Coll_UCA400_CI
  (** [NOCASE] of SQLite: the ASCII letters are folded to lower case *)
  | Coll_ASCII_NoCase.

(** the implicit weights of UCA for a code point which has none in the tables *)
Definition implicit_weights (c : Z) : list Z := [64448 + c / 32768; (c mod 32768) + 32768].

Definition weights_of (coll : collation) (c : Z) : list Z :=
  match coll with
  | Coll_Binary => [c]
  | Coll_General_CI => if c <? 768 then [nth (Z.to_nat c) general_ci_weights c] else if c <? 65536 then [c] else [65533]
  | Coll_UCA900_AI_CI => if c <? 768 then nth (Z.to_nat c) uca900_primary [] else implicit_weights c
  | Coll_UCA520_CI => if c <? 768 then nth (Z.to_nat c) uca520_primary [] else implicit_weights c
  | Coll_UCA400_CI => if c <? 768 then nth (Z.to_nat c) uca400_primary [] else implicit_weights c
  | Coll_ASCII_NoCase => if (65 <=? c) && (c <=? 90) then [c + 32] else [c]
  end.

(** a character which compares as [c] in [LIKE] *)
Definition rep_of (coll : collation) (c : Z) : Z :=
  match coll with
  | Coll_Binary => c
  | Coll_General_CI => if c <? 768 then nth (Z.to_nat c) general_ci_weights c else if c <? 65536 then c else 65533
  | Coll_UCA900_AI_CI => if c <? 768 then nth (Z.to_nat c) uca900_rep c else c
  | Coll_UCA520_CI => if c <? 768 then nth (Z.to_nat c) uca520_rep c else c
  | Coll_UCA400_CI => if c <? 768 then nth (Z.to_nat c) uca400_rep c else c
  | Coll_ASCII_NoCase => if (65 <=? c) && (c <=? 90) then c + 32 else c
  end.

Fixpoint rtrim (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c r => let r' := rtrim r in
                  match r' with EmptyString => if Ascii.eqb c " " then EmptyString else String c EmptyString
                              | _ => String c r' end
  end.

(** the weights, as a string of 2-byte big-endian weights: the comparison of the keys with
    [string_compare] is the lexicographic comparison of the weights *)
Definition weight_string (l : list Z) : string :=
  fold_right (fun w acc => String (ascii_of_nat (Z.to_nat (w / 256))) (String (ascii_of_nat (Z.to_nat (w mod 256))) acc)) EmptyString l.

(** The key of a string: with [PAD SPACE], the trailing spaces are not significant. *)
Definition coll_key (coll : collation) (pad : bool) (s : string) : string :=
  let s := if pad then rtrim s else s in
  match coll with
  | Coll_Binary => s
  | _ => weight_string (flat_map (weights_of coll) (utf8_decode s))
  end.

(** the string in which each character is replaced by its representative, for [LIKE] and the searches
    of substrings ([LOCATE], [INSTR]) *)
Definition coll_fold (coll : collation) (s : string) : string :=
  match coll with
  | Coll_Binary => s
  | _ => utf8_encode (map (rep_of coll) (utf8_decode s))
  end.

(** * [LIKE] and the searches, character by character *)

(** [like_cp esc p s]: [%] matches any sequence of characters, [_] one character, [esc] escapes them *)
Fixpoint like_cp (fuel : nat) (esc : option Z) (p s : list Z) : bool :=
  match fuel with
  | O => false
  | S f =>
    match p with
    | nil => match s with nil => true | _ => false end
    | c :: p' =>
      if (match esc with Some e => c =? e | None => false end)
      then match p', s with
           | d :: p'', x :: s' => (d =? x) && like_cp f esc p'' s'
           | _, _ => false
           end
      else if c =? 37 (* % *)
      then like_cp f esc p' s || match s with _ :: s' => like_cp f esc p s' | nil => false end
      else if c =? 95 (* _ *)
      then match s with _ :: s' => like_cp f esc p' s' | nil => false end
      else match s with x :: s' => (c =? x) && like_cp f esc p' s' | nil => false end
    end
  end.

(** [LIKE] under a collation: each character is compared by its weight; [PAD SPACE] does not apply *)
Definition coll_like (coll : collation) (esc : option Z) (p s : string) : bool :=
  let fp := map (rep_of coll) (utf8_decode p) in
  let fs := map (rep_of coll) (utf8_decode s) in
  like_cp (S (List.length fp) * S (List.length fs))%nat esc fp fs.

Fixpoint prefix_cp (p s : list Z) : bool :=
  match p, s with
  | nil, _ => true
  | x :: p', y :: s' => (x =? y) && prefix_cp p' s'
  | _, _ => false
  end.

(** the position (from 1) of the first occurrence of [sub] in [s], in characters; 0 if none *)
Fixpoint index_cp (i : Z) (sub s : list Z) : Z :=
  if prefix_cp sub s then i
  else match s with nil => 0 | _ :: s' => index_cp (i + 1) sub s' end.

Definition coll_index (coll : collation) (sub s : string) : Z :=
  index_cp 1 (map (rep_of coll) (utf8_decode sub)) (map (rep_of coll) (utf8_decode s)).

(** the number of characters *)
Definition char_count (s : string) : Z := Z.of_nat (List.length (utf8_decode s)).

(** * The names of the collations

    The collations of the MySQL family which the model has, with [PAD SPACE] or not ([NO PAD] for the
    collations of UCA 9.0.0 and [binary]). [utf8mb4_uca1400_ai_ci] of MariaDB is approximated by the
    weights of UCA 9.0.0: the tables of UCA 14.0.0 are generated when MariaDB is built, and are not in
    its source (an open question, recorded in [docs/OPEN_ISSUES.md]). *)
Definition my_collation_of_name (n : string) : option (collation * bool) :=
  match n with
  | "utf8mb4_bin" | "utf8mb3_bin" | "utf8_bin" => Some (Coll_Binary, true)
  | "utf8mb4_0900_bin" | "binary" => Some (Coll_Binary, false)
  | "utf8mb4_general_ci" | "utf8mb3_general_ci" | "utf8_general_ci" => Some (Coll_General_CI, true)
  | "utf8mb4_0900_ai_ci" => Some (Coll_UCA900_AI_CI, false)
  | "utf8mb4_unicode_520_ci" | "utf8mb3_unicode_520_ci" => Some (Coll_UCA520_CI, true)
  | "utf8mb4_unicode_ci" | "utf8mb3_unicode_ci" | "utf8_unicode_ci" => Some (Coll_UCA400_CI, true)
  | "utf8mb4_uca1400_ai_ci" => Some (Coll_UCA900_AI_CI, true)
  | _ => None
  end%string.

(** the collations of SQLite ([BINARY], [NOCASE], [RTRIM]) *)
Definition lite_collation_of_name (n : string) : option (collation * bool) :=
  match n with
  | "BINARY" | "binary" => Some (Coll_Binary, false)
  | "NOCASE" | "nocase" => Some (Coll_ASCII_NoCase, false)
  | "RTRIM" | "rtrim" => Some (Coll_Binary, true)
  | _ => None
  end%string.
