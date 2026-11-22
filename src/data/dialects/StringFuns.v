(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   String functions (TODO 2.2): the algorithms, on the characters (code points)  *)
(**   of a UTF-8 text, and their wrappers, parameterized by the conversions of the  *)
(**   arguments of each dialect.                                                    *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String Ascii ZArith NArith QArith Qcanon Bool.

Require Import Bool3 Values ValueKit Collation Hash.

Import ListNotations.
Import NullValues.
Open Scope Z_scope.
Open Scope bool_scope.

Definition cps := utf8_decode.
Definition txt := utf8_encode.

Definition is_digit_cp (c : Z) := (48 <=? c) && (c <=? 57).
Definition is_upper_cp (c : Z) := (65 <=? c) && (c <=? 90).
Definition is_lower_cp (c : Z) := (97 <=? c) && (c <=? 122).
(** a letter: an ASCII letter, or a character outside ASCII *)
Definition is_alpha_cp (c : Z) := is_upper_cp c || is_lower_cp c || (128 <=? c).
Definition is_alnum_cp (c : Z) := is_alpha_cp c || is_digit_cp c.
(** the case of Latin-1 and Latin Extended-A too ([Collation.upper_cp], TODO 9.7) *)
Definition up_cp (c : Z) := upper_cp c.
Definition low_cp (c : Z) := lower_cp c.
(** the ASCII letters only (SQLite without ICU: [sqlite3UpperToLower], [upper ()] and [LIKE]) *)
Definition ascii_up_cp (c : Z) := if is_lower_cp c then c - 32 else c.
Definition ascii_low_cp (c : Z) := if is_upper_cp c then c + 32 else c.

Fixpoint prefix_of (p s : list Z) : bool :=
  match p, s with
  | nil, _ => true
  | x :: p', y :: s' => (x =? y) && prefix_of p' s'
  | _, _ => false
  end.

(** * Padding: [lpad], [rpad] *)

(** [n] characters: [s] cut, or completed by repetitions of [pad] on the left or the right *)
Definition pad_cp (left : bool) (s : list Z) (n : nat) (pad : list Z) : list Z :=
  let len := List.length s in
  if Nat.leb n len then firstn n s
  else match pad with
       | nil => s
       | _ => let k := (n - len)%nat in
              let p := firstn k (List.concat (repeat pad (S (k / List.length pad)))) in
              if left then p ++ s else s ++ p
       end.

(** * Searches and splits *)

(** the occurrences of [d] in [s], from left to right, and the pieces between them *)
Fixpoint split_aux (fuel : nat) (d s cur : list Z) : list (list Z) :=
  match fuel with
  | O => rev cur :: nil
  | S f =>
    match s with
    | nil => rev cur :: nil
    | c :: r => if prefix_of d s then rev cur :: split_aux f d (skipn (List.length d) s) nil
                else split_aux f d r (c :: cur)
    end
  end.

(** the pieces of [s] separated by [d] (a non-empty separator) *)
Definition split_cp (d s : list Z) : list (list Z) :=
  match d with nil => s :: nil | _ => split_aux (S (List.length s)) d s nil end.

Fixpoint join_cp (d : list Z) (l : list (list Z)) : list Z :=
  match l with nil => nil | x :: nil => x | x :: r => x ++ d ++ join_cp d r end.

(** MySQL [SUBSTRING_INDEX (s, d, n)]: before the [n]-th occurrence of [d] (from the right if [n < 0]) *)
Definition substring_index_cp (s d : list Z) (n : Z) : list Z :=
  match d with
  | nil => nil
  | _ =>
    let parts := split_cp d s in
    let k := Z.of_nat (List.length parts) in
    if n =? 0 then nil
    else if 0 <? n then join_cp d (firstn (Z.to_nat (Z.min n k)) parts)
    else (* from the right: the occurrences are found from the end (they differ when they overlap) *)
         let rparts := split_cp (rev d) (rev s) in
         rev (join_cp (rev d) (firstn (Z.to_nat (Z.min (- n) (Z.of_nat (List.length rparts)))) rparts))
  end.

(** PostgreSQL [split_part (s, d, n)]: the [n]-th piece (from the end if [n < 0]); [''] beyond *)
Definition split_part_cp (s d : list Z) (n : Z) : list Z :=
  let parts := match d with nil => s :: nil | _ => split_cp d s end in
  let parts := match s with nil => nil | _ => parts end in
  let k := Z.of_nat (List.length parts) in
  if 0 <? n then (if k <? n then nil else nth (Z.to_nat (n - 1)) parts nil)
  else if (- n) <=? k then nth (Z.to_nat (k + n)) parts nil else nil.

(** the position (from 1) of the first occurrence of [sub] in [s], 0 if none *)
Fixpoint strpos_aux (i : Z) (sub s : list Z) : Z :=
  if prefix_of sub s then i else match s with nil => 0 | _ :: r => strpos_aux (i + 1) sub r end.
Definition strpos_cp (sub s : list Z) : Z := strpos_aux 1 sub s.

(** * Replacements *)

(** [translate (s, from, to)]: each character of [from] is replaced by the character at the same place
    of [to], or removed when [to] is shorter (its first occurrence in [from] counts) *)
Fixpoint index_of (c : Z) (l : list Z) (i : nat) : option nat :=
  match l with nil => None | x :: r => if x =? c then Some i else index_of c r (S i) end.

Definition translate_cp (s from to : list Z) : list Z :=
  flat_map (fun c => match index_of c from 0 with
                     | Some i => match nth_error to i with Some d => [d] | None => nil end
                     | None => [c]
                     end) s.

(** PostgreSQL [overlay (s placing r from n for k)] *)
Definition overlay_cp (s r : list Z) (n k : Z) : list Z :=
  let len := Z.of_nat (List.length s) in
  firstn (Z.to_nat (Z.min len (n - 1))) s ++ r ++ skipn (Z.to_nat (Z.min len (n - 1 + k))) s.

(** MySQL [INSERT (s, pos, len, new)]: [s] when [pos] is out of the string *)
Definition insert_cp (s r : list Z) (p n : Z) : list Z :=
  let len := Z.of_nat (List.length s) in
  if (p <? 1) || (len <? p) then s
  else let n := if (n <? 0) || (len - p + 1 <? n) then len - p + 1 else n in
       firstn (Z.to_nat (p - 1)) s ++ r ++ skipn (Z.to_nat (p - 1 + n)) s.

(** [initcap]: the first letter or digit of each word in upper case, the others in lower case; the words
    are separated by the characters which are not letters or digits *)
Fixpoint initcap_aux (prev_alnum : bool) (s : list Z) : list Z :=
  match s with
  | nil => nil
  | c :: r => (if prev_alnum then low_cp c else up_cp c) :: initcap_aux (is_alnum_cp c) r
  end.
Definition initcap_cp (s : list Z) : list Z := initcap_aux false s.

(** * Trimming *)
Fixpoint ltrim_set (set s : list Z) : list Z :=
  match s with nil => nil | c :: r => if existsb (Z.eqb c) set then ltrim_set set r else s end.
Definition rtrim_set (set s : list Z) : list Z := rev (ltrim_set set (rev s)).

(** MySQL [TRIM (LEADING r FROM s)]: the string [r] (not a set of characters) is removed as many times as
    it is at the start *)
Fixpoint ltrim_str_aux (fuel : nat) (r s : list Z) : list Z :=
  match fuel, r with
  | O, _ | _, nil => s
  | S f, _ => if prefix_of r s then ltrim_str_aux f r (skipn (List.length r) s) else s
  end.
Definition ltrim_str (r s : list Z) : list Z := ltrim_str_aux (S (List.length s)) r s.
Definition rtrim_str (r s : list Z) : list Z := rev (ltrim_str (rev r) (rev s)).

(** * Quoting *)

(** PostgreSQL [quote_literal]: a backslash makes it an escape string [E'...'] with doubled backslashes *)
Definition quote_literal_cp (s : list Z) : list Z :=
  let q := flat_map (fun c => if c =? 39 then [39; 39] else if c =? 92 then [92; 92] else [c]) s in
  (if existsb (Z.eqb 92) s then [69] else nil) ++ [39] ++ q ++ [39].

(** the reserved key words of PostgreSQL (Appendix C), which [quote_ident] quotes *)
Definition pg_reserved : list string :=
  ["all"; "analyse"; "analyze"; "and"; "any"; "array"; "as"; "asc"; "asymmetric"; "both"; "case"; "cast";
   "check"; "collate"; "column"; "constraint"; "create"; "current_catalog"; "current_date"; "current_role";
   "current_time"; "current_timestamp"; "current_user"; "default"; "deferrable"; "desc"; "distinct"; "do";
   "else"; "end"; "except"; "false"; "fetch"; "for"; "foreign"; "from"; "grant"; "group"; "having"; "in";
   "initially"; "intersect"; "into"; "lateral"; "leading"; "limit"; "localtime"; "localtimestamp"; "not";
   "null"; "offset"; "on"; "only"; "or"; "order"; "placing"; "primary"; "references"; "returning"; "select";
   "session_user"; "some"; "symmetric"; "system_user"; "table"; "then"; "to"; "trailing"; "true"; "union";
   "unique"; "user"; "using"; "variadic"; "when"; "where"; "window"; "with";
   "authorization"; "binary"; "collation"; "concurrently"; "cross"; "current_schema"; "freeze"; "full";
   "ilike"; "inner"; "is"; "isnull"; "join"; "left"; "like"; "natural"; "notnull"; "outer"; "overlaps";
   "right"; "similar"; "tablesample"; "verbose"]%string.

(** [quote_ident]: unquoted if it is a lower-case identifier which is not reserved *)
Definition quote_ident_cp (s : list Z) : list Z :=
  let ok := match s with
            | c :: r => (is_lower_cp c || (c =? 95)) &&
                        forallb (fun x => is_lower_cp x || is_digit_cp x || (x =? 95) || (x =? 36)) r
            | nil => false
            end in
  if ok && negb (existsb (String.eqb (txt s)) pg_reserved) then s
  else [34] ++ flat_map (fun c => if c =? 34 then [34; 34] else [c]) s ++ [34].

(** * MySQL [SOUNDEX] ([Item_func_soundex]): the first letter, then the codes of the following letters,
    a code equal to the previous one or [0] (vowels, [H], [W]) being dropped, completed to 4 characters with
    [0] (the result is not cut to 4 characters) *)
Definition soundex_map : list Z := map (fun c => Z.of_nat (nat_of_ascii c) - 48) (list_ascii_of_string "01230120022455012623010202").

Definition scode (c : Z) : Z :=
  let u := up_cp c in if (65 <=? u) && (u <=? 90) then nth (Z.to_nat (u - 65)) soundex_map 0 else 0.

Fixpoint soundex_rest (last : Z) (s : list Z) : list Z :=
  match s with
  | nil => nil
  | c :: r => if negb (is_alpha_cp c) then soundex_rest last r
              else let k := scode c in
                   if (k =? 0) || (k =? last) then soundex_rest last r else (48 + k) :: soundex_rest k r
  end.

Fixpoint soundex_cp (s : list Z) : list Z :=
  match s with
  | nil => nil
  | c :: r => if is_alpha_cp c
              then let out := up_cp c :: soundex_rest (scode c) r in
                   out ++ repeat 48 (4 - List.length out)
              else soundex_cp r
  end.

(** * Numbers as text *)

(** MySQL [FORMAT (x, d)]: rounded to [d] decimals (at most 30), the integer part grouped by 3 with [,] *)
Fixpoint group3 (l : list ascii) : list ascii :=
  match l with
  | a :: b :: c :: (_ :: _) as r => a :: b :: c :: ","%char :: group3 r
  | _ => l
  end.

Definition format_number (q : Qc) (d : Z) : string :=
  let d := Z.to_nat (Z.min 30 (Z.max 0 d)) in
  let t := dec_text q d in
  let (neg, t) := match t with String "-" r => (true, r) | _ => (false, t) end in
  let ip := match index 0 "." t with Some i => substring 0 i t | None => t end in
  let fp := match index 0 "." t with Some i => substring i (String.length t - i) t | None => EmptyString end in
  let g := string_of_list_ascii (rev (group3 (rev (list_ascii_of_string ip)))) in
  let r := (g ++ fp)%string in
  if neg && negb (forallb (fun c => Ascii.eqb c "0"%char || Ascii.eqb c "."%char || Ascii.eqb c ","%char) (list_ascii_of_string r))
  then ("-" ++ r)%string else r.

(** * PostgreSQL [format (fmt, args...)] ([text_format] in [varlena.c]): [%s] (NULL is empty), [%I]
    ([quote_ident]; NULL is an error), [%L] ([quote_literal], NULL is [NULL]), [%%]; a specifier is
    [%[n$][-][width]type], where the width is a number, [*] (the next argument) or [*n$] (the argument [n]); a
    number which is not followed by [$] right after [%] is a width. A negative width, like the flag [-], pads on
    the right; a NULL width is 0. *)
Fixpoint cp_digits (l : list Z) (acc : Z) (k : nat) : Z * nat :=
  match l with
  | c :: l' => if is_digit_cp c then cp_digits l' (acc * 10 + c - 48) (S k) else (acc, k)
  | nil => (acc, k)
  end.

(** the integer which a text denotes ([pg_strtoint32], without surrounding spaces) *)
Definition cp_int (l : list Z) : option Z :=
  let '(neg, l) := match l with 45 :: r => (true, r) | 43 :: r => (false, r) | _ => (false, l) end in
  match l with
  | nil => None
  | _ => let '(n, k) := cp_digits l 0 0%nat in
         if Nat.eqb k (List.length l) then Some (if neg then - n else n) else None
  end.

Definition pg_pad (s : list Z) (minus : bool) (width : Z) : list Z :=
  let sp := repeat 32 (Z.to_nat (Z.abs width) - List.length s)%nat in
  if minus || (width <? 0) then s ++ sp else sp ++ s.

(** the optional parts of a specifier: the position of the argument, the position of the width ([Some None]: the
    next argument), the flag [-], the direct width, and the rest of the format (which starts with the type) *)
Definition pg_format_spec (r : list Z) : option (option nat * option (option nat) * bool * Z * list Z) :=
  let '(n, k) := cp_digits r 0 0%nat in
  let first :=
      match k, skipn k r with
      | O, _ => Some (None, None, r)
      | _, 36 :: r' => if (0 <? n) then Some (Some (Z.to_nat n - 1)%nat, None, r') else None
      | _, r' => Some (None, Some n, r')
      end in
  match first with
  | None => None
  | Some (argpos, Some w, r) => Some (argpos, None, false, w, r)
  | Some (argpos, None, r) =>
    let fix minus (fuel : nat) (l : list Z) (b : bool) : bool * list Z :=
        match fuel, l with
        | S f, 45 :: l' => minus f l' true
        | _, _ => (b, l)
        end in
    let '(m, r) := minus (List.length r) r false in
    match r with
    | 42 :: r' =>
      let '(n, k) := cp_digits r' 0 0%nat in
      match k, skipn k r' with
      | O, _ => Some (argpos, Some None, m, 0, r')
      | _, 36 :: r'' => if (0 <? n) then Some (argpos, Some (Some (Z.to_nat n - 1)%nat), m, 0, r'') else None
      | _, _ => None
      end
    | _ => let '(n, k) := cp_digits r 0 0%nat in Some (argpos, None, m, n, skipn k r)
    end
  end.

Fixpoint pg_format_aux (fuel : nat) (fmt : list Z) (args : list (option (list Z))) (next : nat) : option (list Z) :=
  match fuel with
  | O => None
  | S f =>
    match fmt with
    | nil => Some nil
    | 37 :: 37 :: r => option_map (cons 37) (pg_format_aux f r args next)
    | 37 :: r =>
      match pg_format_spec r with
      | Some (argpos, wpos, m, w, c :: r') =>
        if (c =? 115) || (c =? 73) || (c =? 76)
        then
          (* the width, and the position after it *)
          let wn := match wpos with
                    | None => Some (w, next)
                    | Some p =>
                      let i := match p with Some i => i | None => next end in
                      match nth_error args i with
                      | Some None => Some (0, S i)
                      | Some (Some t) => match cp_int t with Some z => Some (z, S i) | None => None end
                      | None => None
                      end
                    end in
          match wn with
          | Some (w, next) =>
            let pos := match argpos with Some i => i | None => next end in
            match nth_error args pos with
            | Some a =>
              let piece := if c =? 115 then Some (match a with Some s => s | None => nil end)
                           else if c =? 73 then match a with Some s => Some (quote_ident_cp s) | None => None end
                           else Some (match a with Some s => quote_literal_cp s | None => cps "NULL" end) in
              match piece with
              | Some p => option_map (app (pg_pad p m w)) (pg_format_aux f r' args (S pos))
              | None => None
              end
            | None => None
            end
          | None => None
          end
        else None
      | _ => None
      end
    | c :: r => option_map (cons c) (pg_format_aux f r args next)
    end
  end.

Definition pg_format_string (fmt : list Z) (args : list (option (list Z))) : option (list Z) :=
  pg_format_aux (S (List.length fmt)) fmt args 0.

(** * Characters and codes *)

(** MySQL [ORD]: the bytes of the first character as a big-endian number; [ASCII]: its first byte *)
Definition ord_of (s : string) : Z :=
  match cps s with
  | c :: _ => word_be (bytes_of_string (utf8_encode1 c))
  | nil => 0
  end.

(** MySQL [CHAR (n, ...)]: the bytes of each number, big-endian, without leading zero bytes *)
Fixpoint min_bytes (fuel : nat) (n : Z) : list Z :=
  match fuel with O => nil | S f => if n <=? 0 then nil else min_bytes f (n / 256) ++ [n mod 256] end.
Definition my_char_bytes (n : Z) : list Z := min_bytes 8 (Z.modulo n (2 ^ 32)).

(** * The wrappers

    A dialect gives the text of an argument ([sk_txt]: [None] for NULL), its integer ([sk_int]), the value
    of a text result ([sk_ret]: Oracle makes [''] NULL) and the NULL of a text result. *)
Record skit : Type := mk_skit
  { sk_txt : value -> option string;
    sk_int : value -> option Z;
    sk_ret : string -> value;
    sk_null : value }.

Definition texts (k : skit) (l : list value) : option (list string) :=
  fold_right (fun v acc => match sk_txt k v, acc with Some s, Some r => Some (s :: r) | _, _ => None end) (Some nil) l.

Definition ret_cp (k : skit) (s : list Z) : value := sk_ret k (txt s).

(** [lpad (s, n [, pad])]: [mysql]: a negative [n], or an empty [pad] which must pad, give NULL; otherwise
    (PostgreSQL, Oracle) a non-positive [n] gives [''], an empty [pad] leaves [s] (cut to [n]) *)
Definition f_pad (k : skit) (left mysql : bool) (l : list value) : value :=
  match l with
  | s :: n :: rest =>
    let pad := match rest with p :: nil => sk_txt k p | nil => Some " "%string | _ => None end in
    match sk_txt k s, sk_int k n, pad with
    | Some s, Some n, Some p =>
      let s := cps s in let p := cps p in
      if n <? 0 then (if mysql then sk_null k else sk_ret k EmptyString)
      else if mysql && (Z.of_nat (List.length s) <? n) && (match p with nil => true | _ => false end) then sk_null k
      else ret_cp k (pad_cp left s (Z.to_nat n) p)
    | _, _, _ => sk_null k
    end
  | _ => Value_Err "wrong number of arguments"
  end.

Definition f_substring_index (k : skit) (l : list value) : value :=
  match l with
  | s :: d :: n :: nil => match sk_txt k s, sk_txt k d, sk_int k n with
                          | Some s, Some d, Some n => ret_cp k (substring_index_cp (cps s) (cps d) n)
                          | _, _, _ => sk_null k end
  | _ => Value_Err "wrong number of arguments"
  end.

Definition f_split_part (k : skit) (l : list value) : value :=
  match l with
  | s :: d :: n :: nil => match sk_txt k s, sk_txt k d, sk_int k n with
                          | Some s, Some d, Some n =>
                            if n =? 0 then Value_Err "field position must not be zero"
                            else ret_cp k (split_part_cp (cps s) (cps d) n)
                          | _, _, _ => sk_null k end
  | _ => Value_Err "wrong number of arguments"
  end.

Definition f_translate (k : skit) (l : list value) : value :=
  match texts k l with
  | Some (s :: a :: b :: nil) => ret_cp k (translate_cp (cps s) (cps a) (cps b))
  | Some _ => Value_Err "wrong number of arguments"
  | None => sk_null k
  end.

Definition f_text1 (k : skit) (f : list Z -> list Z) (l : list value) : value :=
  match texts k l with
  | Some (s :: nil) => ret_cp k (f (cps s))
  | Some _ => Value_Err "wrong number of arguments"
  | None => sk_null k
  end.

Definition f_overlay (k : skit) (l : list value) : value :=
  match l with
  | s :: r :: n :: rest =>
    match sk_txt k s, sk_txt k r, sk_int k n,
          match rest with nil => Some None | m :: nil => option_map Some (sk_int k m) | _ => None end with
    | Some s, Some r, Some n, Some m =>
      let r := cps r in
      let m := match m with Some m => m | None => Z.of_nat (List.length r) end in
      if n <? 1 then Value_Err "negative substring length not allowed"
      else ret_cp k (overlay_cp (cps s) r n m)
    | _, _, _, _ => sk_null k
    end
  | _ => Value_Err "wrong number of arguments"
  end.

Definition f_insert (k : skit) (l : list value) : value :=
  match l with
  | s :: p :: n :: r :: nil =>
    match sk_txt k s, sk_int k p, sk_int k n, sk_txt k r with
    | Some s, Some p, Some n, Some r => ret_cp k (insert_cp (cps s) (cps r) p n)
    | _, _, _, _ => sk_null k
    end
  | _ => Value_Err "wrong number of arguments"
  end.

(** [strpos (s, sub)] (PostgreSQL); [position] is the same with the arguments the other way *)
Definition f_strpos (k : skit) (l : list value) : value :=
  match texts k l with
  | Some (s :: sub :: nil) => Value_Z (Some (strpos_cp (cps sub) (cps s)))
  | Some _ => Value_Err "wrong number of arguments"
  | None => Value_Z None
  end.

(** trimming a set of characters: [where] 0 both, 1 leading, 2 trailing; the set is the second argument
    (a space by default) *)
Definition f_trim_set (k : skit) (where_ : nat) (l : list value) : value :=
  match texts k l with
  | Some (s :: rest) =>
    let set := match rest with c :: _ => cps c | nil => [32] end in
    let s := cps s in
    ret_cp k (match where_ with
              | O => rtrim_set set (ltrim_set set s)
              | 1%nat => ltrim_set set s
              | _ => rtrim_set set s
              end)
  | Some nil => Value_Err "wrong number of arguments"
  | None => sk_null k
  end.

(** MySQL [TRIM ([BOTH | LEADING | TRAILING] r FROM s)]: [r] is a string *)
Definition f_trim_str (k : skit) (where_ : nat) (l : list value) : value :=
  match texts k l with
  | Some (s :: r :: nil) =>
    let s := cps s in let r := cps r in
    ret_cp k (match where_ with
              | O => rtrim_str r (ltrim_str r s)
              | 1%nat => ltrim_str r s
              | _ => rtrim_str r s
              end)
  (* [TRIM (LEADING FROM s)], without the string to remove: the spaces *)
  | Some (s :: nil) =>
    let s := cps s in let r := 32 :: nil in
    ret_cp k (match where_ with
              | O => rtrim_str r (ltrim_str r s)
              | 1%nat => ltrim_str r s
              | _ => rtrim_str r s
              end)
  | Some _ => Value_Err "wrong number of arguments"
  | None => sk_null k
  end.

(** [concat_ws] of PostgreSQL and SQLite: the NULL arguments are skipped; a NULL separator gives NULL *)
Definition f_concat_ws (k : skit) (l : list value) : value :=
  match l with
  | sep :: rest =>
    match sk_txt k sep with
    | Some sp => sk_ret k (txt (join_cp (cps sp) (flat_map (fun v => match sk_txt k v with Some s => [cps s] | None => nil end) rest)))
    | None => sk_null k
    end
  | nil => Value_Err "wrong number of arguments"
  end.

Definition f_space (k : skit) (l : list value) : value :=
  match l with
  | n :: nil => match sk_int k n with Some n => sk_ret k (txt (repeat 32 (Z.to_nat n))) | None => sk_null k end
  | _ => Value_Err "wrong number of arguments"
  end.

(** MySQL [ELT (n, s1, ...)], [FIELD (s, s1, ...)], [FIND_IN_SET (s, list)] *)
Definition f_elt (k : skit) (l : list value) : value :=
  match l with
  | n :: rest => match sk_int k n with
                 | Some n => if n <? 1 then sk_null k
                             else match (if Z.of_nat (List.length rest) <? n then None else nth_error rest (Z.to_nat (n - 1))) with
                                  | Some v => match sk_txt k v with Some s => sk_ret k s | None => sk_null k end
                                  | None => sk_null k end
                 | None => sk_null k end
  | nil => Value_Err "wrong number of arguments"
  end.

Definition f_field (k : skit) (eq : string -> string -> bool) (l : list value) : value :=
  match l with
  | s :: rest => match sk_txt k s with
                 | Some s => let fix go (i : Z) (r : list value) :=
                                 match r with
                                 | nil => 0
                                 | v :: r' => match sk_txt k v with Some t => if eq s t then i else go (i + 1) r' | None => go (i + 1) r' end
                                 end in
                             Value_Z (Some (go 1 rest))
                 | None => Value_Z (Some 0) end
  | nil => Value_Err "wrong number of arguments"
  end.

Definition f_find_in_set (k : skit) (eq : string -> string -> bool) (l : list value) : value :=
  match l with
  | s :: set :: nil =>
    match sk_txt k s, sk_txt k set with
    | Some s, Some set =>
      if existsb (Z.eqb 44) (cps s) then Value_Z (Some 0)
      else let parts := match set with EmptyString => nil | _ => split_cp [44] (cps set) end in
           let fix go (i : Z) (r : list (list Z)) :=
               match r with nil => 0 | p :: r' => if eq s (txt p) then i else go (i + 1) r' end in
           Value_Z (Some (go 1 parts))
    | _, _ => Value_Z None
    end
  | _ => Value_Err "wrong number of arguments"
  end.

(** digests, as hexadecimal text ([md5], [sha1], MySQL [sha2 (s, bits)]) *)
Definition f_digest (k : skit) (h : list Z -> list Z) (l : list value) : value :=
  match texts k l with
  | Some (s :: nil) => sk_ret k (hex_of_bytes false (h (bytes_of_string s)))
  | Some _ => Value_Err "wrong number of arguments"
  | None => sk_null k
  end.

Definition f_sha2 (k : skit) (l : list value) : value :=
  match l with
  | s :: n :: nil =>
    match sk_txt k s, sk_int k n with
    | Some s, Some n =>
      let b := bytes_of_string s in
      match n with
      | 0 | 256 => sk_ret k (hex_of_bytes false (sha256 b))
      | 224 => sk_ret k (hex_of_bytes false (sha224 b))
      | 384 => sk_ret k (hex_of_bytes false (sha384 b))
      | 512 => sk_ret k (hex_of_bytes false (sha512 b))
      | _ => sk_null k
      end
    | _, _ => sk_null k
    end
  | _ => Value_Err "wrong number of arguments"
  end.

(** * [LIKE ... ESCAPE e] and [ILIKE]

    [fold] maps each character before the match (lower case for [ILIKE] and for SQLite, the representative
    of the collation for the MySQL family); [dflt] is the escape character without [ESCAPE] ([\] in
    PostgreSQL and the MySQL family, none in SQLite and Oracle). An empty [ESCAPE ''] means no escape
    character in PostgreSQL and MySQL; an escape of more than one character is an error ([bad_escape]). *)
Definition like_pred (k : skit) (null_dflt : bool) (fold : Z -> Z) (dflt : option Z) (l : list value) : bool3 :=
  match l with
  | v :: p :: rest =>
    match sk_txt k v, sk_txt k p,
          match rest with nil => Some dflt
                     | e :: nil => match sk_txt k e with
                                   | Some e => match cps e with c :: nil => Some (Some c) | _ => Some None end
                                   (* MySQL: [ESCAPE NULL] is the default escape *)
                                   | None => if null_dflt then Some dflt else None end
                     | _ => None end with
    | Some s, Some p, Some esc =>
      let fp := map fold (cps p) in
      let fs := map fold (cps s) in
      bool3_of_bool (like_cp (S (List.length fp) * S (List.length fs)) esc fp fs)
    | _, _, _ => unknown3
    end
  | _ => unknown3
  end.

Definition bad_escape (k : skit) (p : string) (l : list value) : bool :=
  existsb (String.eqb p) ("like_escape" :: "not like_escape" :: "ilike_escape" :: "not ilike_escape" :: nil)%string &&
  match l with
  | _ :: _ :: e :: nil => match sk_txt k e with Some e => Nat.ltb 1 (List.length (cps e)) | None => false end
  | _ => false
  end.

Definition like_table (k : skit) (null_dflt : bool) (fold ifold : Z -> Z) (dflt : option Z) : list (string * (list value -> bool3)) :=
     ("like_escape", like_pred k null_dflt fold dflt)
  :: ("not like_escape", fun l => negb3 (like_pred k null_dflt fold dflt l))
  :: ("ilike", like_pred k null_dflt ifold dflt) :: ("not ilike", fun l => negb3 (like_pred k null_dflt ifold dflt l))
  :: ("ilike_escape", like_pred k null_dflt ifold dflt) :: ("not ilike_escape", fun l => negb3 (like_pred k null_dflt ifold dflt l))
  :: nil.
