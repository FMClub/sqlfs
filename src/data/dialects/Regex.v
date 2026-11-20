(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Regular expressions (TODO 2.4): one abstract syntax, a parser per syntax      *)
(**   (PostgreSQL ARE, ICU of MySQL, PCRE of MariaDB, RE2 of TiDB, Oracle), and a   *)
(**   backtracking matcher which gives the matches in the order of preference.      *)
(**                                                                                 *)
(************************************************************************************)

Require Import List ZArith Bool.

Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

(** * Syntax *)

(** an item of a bracket expression, or a class escape *)
Inductive citem : Type :=
  | CI_Range : Z -> Z -> citem          (** a character or a range [a-z] *)
  | CI_Digit | CI_Word | CI_Space        (** [\d], [\w], [\s], [[:digit:]], ... *)
  | CI_Alpha | CI_Upper | CI_Lower | CI_Alnum | CI_Punct | CI_XDigit
  | CI_Not : citem -> citem.             (** [\D], [\W], [\S] *)

Inductive re : Type :=
  | R_Empty : re
  | R_Char : Z -> re
  | R_Any : re                                       (** [.] *)
  | R_Set : bool -> list citem -> re                 (** [[...]], [true]: negated *)
  | R_Seq : re -> re -> re
  | R_Alt : re -> re -> re
  | R_Rep : re -> nat -> option nat -> bool -> re    (** min, max, greedy *)
  | R_Group : nat -> re -> re                        (** a capturing group, numbered from 1 *)
  | R_Back : nat -> re                               (** a back reference *)
  | R_Bol : re | R_Eol : re                          (** [^], [$] (lines in multi-line mode) *)
  | R_Start : re | R_End : re                        (** [\A], [\z] *)
  | R_WordB : bool -> re                             (** [\b] ([true]) and [\B] *)
  | R_WordStart : re | R_WordEnd : re                (** PostgreSQL [\m], [\M] *)
  | R_Look : bool -> re -> re                        (** lookahead [(?=r)] ([true]), [(?!r)] *)
  | R_LookB : bool -> re -> re.                      (** lookbehind [(?<=r)] ([true]), [(?<!r)] *)

(** the options of a match *)
Record ropts : Type := mk_ropts
  { o_icase : bool;       (** case-insensitive (ASCII letters) *)
    o_multiline : bool;   (** [^] and [$] at the line breaks *)
    o_dotnl : bool }.     (** [.] matches a line break *)

(** * Characters *)
Definition is_digit (c : Z) := (48 <=? c) && (c <=? 57).
Definition is_upper (c : Z) := (65 <=? c) && (c <=? 90).
Definition is_lower (c : Z) := (97 <=? c) && (c <=? 122).
Definition is_alpha (c : Z) := is_upper c || is_lower c || (170 <=? c).
Definition is_word (c : Z) := is_alpha c || is_digit c || (c =? 95).
Definition is_space (c : Z) := (c =? 32) || ((9 <=? c) && (c <=? 13)).
Definition is_punct (c : Z) := ((33 <=? c) && (c <=? 47)) || ((58 <=? c) && (c <=? 64))
                               || ((91 <=? c) && (c <=? 96)) || ((123 <=? c) && (c <=? 126)).
Definition is_xdigit (c : Z) := is_digit c || ((65 <=? c) && (c <=? 70)) || ((97 <=? c) && (c <=? 102)).
Definition fold (c : Z) := if is_upper c then c + 32 else c.

Fixpoint citem_match (o : ropts) (c : Z) (i : citem) : bool :=
  match i with
  | CI_Range lo hi => ((lo <=? c) && (c <=? hi)) ||
                      (o_icase o && (((lo <=? fold c) && (fold c <=? hi)) ||
                                     (is_lower c && (lo <=? c - 32) && (c - 32 <=? hi))))
  | CI_Digit => is_digit c | CI_Word => is_word c | CI_Space => is_space c
  | CI_Alpha => is_alpha c | CI_Upper => is_upper c || (o_icase o && is_lower c)
  | CI_Lower => is_lower c || (o_icase o && is_upper c) | CI_Alnum => is_alpha c || is_digit c
  | CI_Punct => is_punct c | CI_XDigit => is_xdigit c
  | CI_Not i => negb (citem_match o c i)
  end.

(** * Matching

    A state is a position and the captured groups. [m fuel r st] is the list of the states after a match
    of [r] from [st], in the order of preference of a backtracking engine (a greedy repetition prefers
    one more iteration, a lazy one prefers one less); an iteration of a repetition which matches the
    empty string ends it. *)
Definition caps := list (option (nat * nat)).
Definition state := (nat * caps)%type.

Fixpoint set_cap (n : nat) (v : nat * nat) (l : caps) : caps :=
  match n, l with
  | O, _ :: r => Some v :: r
  | O, nil => Some v :: nil
  | S k, x :: r => x :: set_cap k v r
  | S k, nil => None :: set_cap k v nil
  end.

(** equal states: the later ones are dropped (the order of preference is kept); this bounds the number of
    states of nested repetitions which can match the empty string *)
Definition opt_pair_eqb (a b : option (nat * nat)) : bool :=
  match a, b with
  | Some (x, y), Some (u, v) => Nat.eqb x u && Nat.eqb y v
  | None, None => true
  | _, _ => false
  end.

Fixpoint caps_eqb (a b : caps) : bool :=
  match a, b with
  | x :: a', y :: b' => opt_pair_eqb x y && caps_eqb a' b'
  | nil, nil => true
  | _, _ => false
  end.

Definition state_eqb (a b : state) : bool := Nat.eqb (fst a) (fst b) && caps_eqb (snd a) (snd b).

Fixpoint dedup_states (seen : list state) (l : list state) : list state :=
  match l with
  | nil => nil
  | x :: r => if existsb (state_eqb x) seen then dedup_states seen r else x :: dedup_states (x :: seen) r
  end.

Section Match.
Variable o : ropts.
Variable s : list Z.
Let len := List.length s.
Definition at_ (i : nat) : option Z := nth_error s i.

Definition is_nl (i : nat) : bool := match at_ i with Some 10 => true | _ => false end.
Definition word_at (i : nat) : bool := match at_ i with Some c => is_word c | None => false end.
Definition word_before (i : nat) : bool := match i with O => false | S k => word_at k end.

Fixpoint sub_eq (i j : nat) (n : nat) : bool :=
  match n with
  | O => true
  | S k => match at_ i, at_ j with
           | Some a, Some b => (if o_icase o then fold a =? fold b else a =? b) && sub_eq (S i) (S j) k
           | _, _ => false
           end
  end.

Fixpoint m (fuel : nat) (r : re) (st : state) {struct fuel} : list state :=
  match fuel with
  | O => nil
  | S f =>
    let (i, cs) := st in
    let one (ok : Z -> bool) := match at_ i with Some c => if ok c then [(S i, cs)] else nil | None => nil end in
    match r with
    | R_Empty => [st]
    | R_Char c => one (fun x => if o_icase o then fold x =? fold c else x =? c)
    | R_Any => one (fun x => o_dotnl o || negb (x =? 10))
    | R_Set neg items => one (fun x => xorb neg (existsb (citem_match o x) items))
    | R_Seq a b => flat_map (m f b) (m f a st)
    | R_Alt a b => m f a st ++ m f b st
    | R_Rep a mn mx g =>
      match mn with
      | S mn' => dedup_states nil (flat_map (m f (R_Rep a mn' (option_map pred mx) g)) (m f a st))
      | O =>
        match mx with
        | Some O => [st]
        | _ =>
          (* an iteration which matches the empty string ends the repetition (it is kept once) *)
          let more := flat_map (fun st' => if Nat.eqb (fst st') i then [st']
                                           else m f (R_Rep a 0 (option_map pred mx) g) st') (m f a st) in
          dedup_states nil (if g then more ++ [st] else st :: more)
        end
      end
    | R_Group n a => map (fun st' => (fst st', set_cap (pred n) (i, fst st') (snd st'))) (m f a st)
    | R_Back n => match nth_error cs (pred n) with
                  | Some (Some (b, e)) => let k := (e - b)%nat in
                                          if sub_eq b i k then [((i + k)%nat, cs)] else nil
                  | _ => nil  (* a group which did not take part in the match matches nothing *)
                  end
    | R_Bol => if Nat.eqb i 0 || (o_multiline o && match i with S k => is_nl k | O => false end) then [st] else nil
    | R_Eol => if Nat.eqb i len || (o_multiline o && is_nl i) then [st] else nil
    | R_Start => if Nat.eqb i 0 then [st] else nil
    | R_End => if Nat.eqb i len then [st] else nil
    | R_WordB b => if Bool.eqb b (xorb (word_before i) (word_at i)) then [st] else nil
    | R_WordStart => if negb (word_before i) && word_at i then [st] else nil
    | R_WordEnd => if word_before i && negb (word_at i) then [st] else nil
    | R_Look pos a => if Bool.eqb pos (match m f a st with nil => false | _ => true end) then [st] else nil
    | R_LookB pos a =>
      let found := existsb (fun j => existsb (fun st' => Nat.eqb (fst st') i) (m f a (j, cs))) (seq 0 (S i)) in
      if Bool.eqb pos found then [st] else nil
    end
  end.

End Match.

Fixpoint re_size (r : re) : nat :=
  match r with
  | R_Seq a b | R_Alt a b => S (re_size a + re_size b)
  | R_Rep a _ _ _ | R_Group _ a | R_Look _ a | R_LookB _ a => S (re_size a)
  | _ => 1
  end.

Fixpoint ngroups (r : re) : nat :=
  match r with
  | R_Seq a b | R_Alt a b => Nat.max (ngroups a) (ngroups b)
  | R_Rep a _ _ _ | R_Look _ a | R_LookB _ a => ngroups a
  | R_Group n a => Nat.max n (ngroups a)
  | _ => 0
  end.

(** the fuel: the depth of the recursion is bounded by the size of the expression times the length of
    the text (each iteration of a repetition consumes a character) *)
Definition fuel_for (r : re) (s : list Z) : nat := (S (re_size r) * S (List.length s) * 2 + 10)%nat.

(** * Choosing a match

    [Leftmost_First]: the first match in the order of preference, at the leftmost position where there is
    one (Perl, PCRE, ICU, RE2, Oracle). [Leftmost_Greediness g]: at the leftmost position, the longest
    match if the expression is greedy, the shortest if not (PostgreSQL ARE, [regex/regexec.c]); the
    groups are those of the first such match in the order of preference. *)
Inductive policy : Type := Leftmost_First | Leftmost_Greediness : bool -> policy.

(** a match: its start, its end, and the groups *)
Definition rmatch := (nat * nat * caps)%type.

Definition best (p : policy) (start : nat) (l : list state) : option rmatch :=
  match l with
  | nil => None
  | (e, cs) :: _ =>
    match p with
    | Leftmost_First => Some (start, e, cs)
    | Leftmost_Greediness g =>
      let pick := fold_left (fun acc st => if (if g then Nat.ltb (fst acc) (fst st) else Nat.ltb (fst st) (fst acc))
                                          then st else acc) l (e, cs) in
      Some (start, fst pick, snd pick)
    end
  end.

Fixpoint search_from (o : ropts) (p : policy) (r : re) (s : list Z) (i : nat) (fuel : nat) : option rmatch :=
  match fuel with
  | O => None
  | S f =>
    match best p i (m o s (fuel_for r s) r (i, repeat None (ngroups r))) with
    | Some x => Some x
    | None => if Nat.leb (List.length s) i then None else search_from o p r s (S i) f
    end
  end.

(** the first match at or after position [i] *)
Definition search (o : ropts) (p : policy) (r : re) (s : list Z) (i : nat) : option rmatch :=
  search_from o p r s i (S (List.length s - i)).

(** all the matches, from position [i], without overlap; after an empty match the search goes on one
    character further *)
Fixpoint all_matches (o : ropts) (p : policy) (r : re) (s : list Z) (i : nat) (fuel : nat) : list rmatch :=
  match fuel with
  | O => nil
  | S f =>
    match search o p r s i with
    | Some (b, e, cs) =>
      (b, e, cs) :: (if Nat.leb (List.length s) e && Nat.eqb b e then nil
                     else all_matches o p r s (if Nat.eqb b e then S e else e) f)
    | None => nil
    end
  end.

Definition matches (o : ropts) (p : policy) (r : re) (s : list Z) (i : nat) : list rmatch :=
  all_matches o p r s i (S (S (List.length s))).

(** * The greediness of a PostgreSQL ARE ([regex/regcomp.c], "Matching Rules" of the manual): a branch has
    the greediness of its first quantified atom which has one ([{m}] keeps the one of its atom), an
    alternation of several branches is greedy, and an expression without any attribute is greedy *)
Fixpoint greediness (r : re) : option bool :=
  match r with
  | R_Alt _ _ => Some true
  | R_Seq a b => match greediness a with Some g => Some g | None => greediness b end
  | R_Rep a mn mx g => match mx with
                       | Some k => if Nat.eqb mn k then greediness a else Some g
                       | None => Some g
                       end
  | R_Group _ a => greediness a
  | _ => None
  end.

Definition pg_policy (r : re) : policy :=
  Leftmost_Greediness (match greediness r with Some g => g | None => true end).

(** * Parsing

    The syntaxes differ in a few escapes: [flav_pg] reads [\y], [\Y], [\m], [\M] as word boundaries and
    [\b] as a backspace (ARE); [flav_backref] allows back references ([\1] .. [\9]: not in RE2);
    [flav_look] allows lookaheads. *)
Record flavor : Type := mk_flavor { flav_pg : bool; flav_backref : bool; flav_look : bool }.

Definition class_esc (c : Z) : option citem :=
  if c =? 100 then Some CI_Digit else if c =? 68 then Some (CI_Not CI_Digit)
  else if c =? 119 then Some CI_Word else if c =? 87 then Some (CI_Not CI_Word)
  else if c =? 115 then Some CI_Space else if c =? 83 then Some (CI_Not CI_Space)
  else None.

(** a character escape: [\n], [\t], [\r], [\f], [\v], [\e], or the character itself *)
Definition char_esc (c : Z) : Z :=
  if c =? 110 then 10 else if c =? 116 then 9 else if c =? 114 then 13 else if c =? 102 then 12
  else if c =? 118 then 11 else if c =? 101 then 27 else c.

Definition posix_class (name : list Z) : option citem :=
  let n := name in
  if list_eq_dec Z.eq_dec n [97;108;112;104;97] then Some CI_Alpha            (* alpha *)
  else if list_eq_dec Z.eq_dec n [100;105;103;105;116] then Some CI_Digit     (* digit *)
  else if list_eq_dec Z.eq_dec n [97;108;110;117;109] then Some CI_Alnum      (* alnum *)
  else if list_eq_dec Z.eq_dec n [117;112;112;101;114] then Some CI_Upper     (* upper *)
  else if list_eq_dec Z.eq_dec n [108;111;119;101;114] then Some CI_Lower     (* lower *)
  else if list_eq_dec Z.eq_dec n [115;112;97;99;101] then Some CI_Space       (* space *)
  else if list_eq_dec Z.eq_dec n [112;117;110;99;116] then Some CI_Punct      (* punct *)
  else if list_eq_dec Z.eq_dec n [120;100;105;103;105;116] then Some CI_XDigit (* xdigit *)
  else if list_eq_dec Z.eq_dec n [119;111;114;100] then Some CI_Word          (* word *)
  else if list_eq_dec Z.eq_dec n [98;108;97;110;107] then Some (CI_Range 32 32) (* blank (approx: space) *)
  else None.

Fixpoint take_until (c : Z) (l : list Z) (acc : list Z) : option (list Z * list Z) :=
  match l with
  | nil => None
  | x :: r => if x =? c then Some (rev acc, r) else take_until c r (x :: acc)
  end.

(** the items of a bracket expression, up to its [\]] (a [\]] first is a character) *)
Fixpoint parse_bracket (fl : flavor) (fuel : nat) (l : list Z) (first : bool) (acc : list citem)
  : option (list citem * list Z) :=
  match fuel with
  | O => None
  | S f =>
    match l with
    | nil => None
    | 93 :: r => if first then parse_bracket fl f r false (CI_Range 93 93 :: acc) else Some (rev acc, r)
    | 91 :: 58 :: r =>  (* [:name:] *)
      match take_until 58 r nil with
      | Some (name, 93 :: r') => match posix_class name with
                                 | Some ci => parse_bracket fl f r' false (ci :: acc)
                                 | None => None end
      | _ => parse_bracket fl f (58 :: r) false (CI_Range 91 91 :: acc)
      end
    | 92 :: c :: r =>
      match class_esc c with
      | Some ci => parse_bracket fl f r false (ci :: acc)
      | None => let ch := char_esc c in
                match r with
                | 45 :: d :: r' => if d =? 93 then parse_bracket fl f (93 :: r') false (CI_Range 45 45 :: CI_Range ch ch :: acc)
                                   else parse_bracket fl f r' false (CI_Range ch d :: acc)
                | _ => parse_bracket fl f r false (CI_Range ch ch :: acc)
                end
      end
    | c :: 45 :: d :: r => if d =? 93 then parse_bracket fl f (93 :: r) false (CI_Range 45 45 :: CI_Range c c :: acc)
                           else let (d, r) := match r with e :: r' => if d =? 92 then (char_esc e, r') else (d, r) | nil => (d, r) end in
                                if d <? c then None
                                else parse_bracket fl f r false (CI_Range c d :: acc)
    | c :: r => parse_bracket fl f r false (CI_Range c c :: acc)
    end
  end.

Fixpoint parse_int (l : list Z) (acc : Z) (seen : bool) : option (Z * list Z) :=
  match l with
  | c :: r => if is_digit c then parse_int r (acc * 10 + c - 48) true else if seen then Some (acc, l) else None
  | nil => if seen then Some (acc, nil) else None
  end.

(** [{m}], [{m,}], [{m,n}] after the [{] *)
Definition parse_bound (l : list Z) : option (nat * option nat * list Z) :=
  match parse_int l 0 false with
  | Some (m, 125 :: r) => Some (Z.to_nat m, Some (Z.to_nat m), r)
  | Some (m, 44 :: 125 :: r) => Some (Z.to_nat m, None, r)
  | Some (m, 44 :: r) => match parse_int r 0 false with
                         | Some (n, 125 :: r') => if n <? m then None else Some (Z.to_nat m, Some (Z.to_nat n), r')
                         | _ => None end
  | _ => None
  end.

(** case folding of a sub-pattern, for the scoped inline flag [(?i:...)] and [((?i)...)]: a letter matches
    its two cases, and the letter ranges of a class are completed with their other case (the back
    references of the sub-pattern stay case-sensitive) *)
Definition other_case_ranges (it : citem) : list citem :=
  match it with
  | CI_Range a b =>
    (if Z.leb (Z.max a 97) (Z.min b 122) then CI_Range (Z.max a 97 - 32) (Z.min b 122 - 32) :: nil else nil) ++
    (if Z.leb (Z.max a 65) (Z.min b 90) then CI_Range (Z.max a 65 + 32) (Z.min b 90 + 32) :: nil else nil)
  | CI_Upper | CI_Lower => CI_Alpha :: nil
  | _ => nil
  end.

Fixpoint ci_re (r : re) : re :=
  match r with
  | R_Char c => if is_upper c || is_lower c then R_Set false (CI_Range (fold c) (fold c) :: CI_Range (fold c - 32) (fold c - 32) :: nil) else r
  | R_Set neg items => R_Set neg (items ++ flat_map other_case_ranges items)
  | R_Seq a b => R_Seq (ci_re a) (ci_re b)
  | R_Alt a b => R_Alt (ci_re a) (ci_re b)
  | R_Rep a mn mx g => R_Rep (ci_re a) mn mx g
  | R_Group n a => R_Group n (ci_re a)
  | R_Look b a => R_Look b (ci_re a)
  | R_LookB b a => R_LookB b (ci_re a)
  | _ => r
  end.

Section Parse.
Variable fl : flavor.

(** the parser: [alt] and [seq] read up to a [)] or the end; the group counter is threaded *)
Fixpoint p_alt (fuel : nat) (l : list Z) (g : nat) {struct fuel} : option (re * list Z * nat) :=
  match fuel with
  | O => None
  | S f =>
    match p_seq f l g R_Empty with
    | Some (a, 124 :: r, g') => match p_alt f r g' with
                                | Some (b, r', g'') => Some (R_Alt a b, r', g'')
                                | None => None end
    | x => x
    end
  end

with p_seq (fuel : nat) (l : list Z) (g : nat) (acc : re) {struct fuel} : option (re * list Z * nat) :=
  match fuel with
  | O => None
  | S f =>
    match l with
    | nil => Some (acc, nil, g)
    | 124 :: _ | 41 :: _ => Some (acc, l, g)
    | _ =>
      match p_atom f l g with
      | Some (a, r, g') =>
        match p_quant f a r with
        | Some (q, r') => p_seq f r' g' (match acc with R_Empty => q | _ => R_Seq acc q end)
        | None => None
        end
      | None => None
      end
    end
  end

with p_quant (fuel : nat) (a : re) (l : list Z) {struct fuel} : option (re * list Z) :=
  match fuel with
  | O => None
  | S f =>
    let lazy (mn : nat) (mx : option nat) (r : list Z) :=
        match r with
        | 63 :: r' => p_quant f (R_Rep a mn mx false) r'
        | 43 :: r' => if flav_pg fl then None else p_quant f (R_Rep a mn mx true) r'   (* possessive: as greedy *)
        | _ => p_quant f (R_Rep a mn mx true) r
        end in
    match l with
    | 42 :: r => lazy 0%nat None r
    | 43 :: r => lazy 1%nat None r
    | 63 :: r => lazy 0%nat (Some 1%nat) r
    | 123 :: r => match parse_bound r with
                  | Some (mn, mx, r') => lazy mn mx r'
                  | None => Some (a, l)  (* a [{] which is not a bound is a character (handled by the atom) *)
                  end
    | _ => Some (a, l)
    end
  end

with p_atom (fuel : nat) (l : list Z) (g : nat) {struct fuel} : option (re * list Z * nat) :=
  match fuel with
  | O => None
  | S f =>
    match l with
    (* the scoped flag [i]: [(?i:r)], [(?:(?i)r)] and [((?i)r)] (ICU, PCRE, RE2) *)
    | 40 :: 63 :: 105 :: 58 :: r =>
      match p_alt f r g with Some (a, 41 :: r', g') => Some (ci_re a, r', g') | _ => None end
    | 40 :: 63 :: 58 :: 40 :: 63 :: 105 :: 41 :: r =>
      match p_alt f r g with Some (a, 41 :: r', g') => Some (ci_re a, r', g') | _ => None end
    | 40 :: 40 :: 63 :: 105 :: 41 :: r =>
      let n := S g in
      match p_alt f r n with Some (a, 41 :: r', g') => Some (R_Group n (ci_re a), r', g') | _ => None end
    | 40 :: 63 :: 58 :: r =>   (* (?: *)
      match p_alt f r g with Some (a, 41 :: r', g') => Some (a, r', g') | _ => None end
    | 40 :: 63 :: 61 :: r =>   (* (?= *)
      if flav_look fl then match p_alt f r g with Some (a, 41 :: r', g') => Some (R_Look true a, r', g') | _ => None end else None
    | 40 :: 63 :: 33 :: r =>   (* (?! *)
      if flav_look fl then match p_alt f r g with Some (a, 41 :: r', g') => Some (R_Look false a, r', g') | _ => None end else None
    | 40 :: 63 :: 60 :: 61 :: r =>   (* (?<= *)
      if flav_look fl then match p_alt f r g with Some (a, 41 :: r', g') => Some (R_LookB true a, r', g') | _ => None end else None
    | 40 :: 63 :: 60 :: 33 :: r =>   (* (?<! *)
      if flav_look fl then match p_alt f r g with Some (a, 41 :: r', g') => Some (R_LookB false a, r', g') | _ => None end else None
    | 40 :: 63 :: _ => None
    | 40 :: r => let n := S g in
                 match p_alt f r n with Some (a, 41 :: r', g') => Some (R_Group n a, r', g') | _ => None end
    | 46 :: r => Some (R_Any, r, g)
    | 94 :: r => Some (R_Bol, r, g)
    | 36 :: r => Some (R_Eol, r, g)
    | 91 :: 94 :: r => match parse_bracket fl (S (List.length r)) r true nil with
                       | Some (items, r') => Some (R_Set true items, r', g) | None => None end
    | 91 :: r => match parse_bracket fl (S (List.length r)) r true nil with
                 | Some (items, r') => Some (R_Set false items, r', g) | None => None end
    | 92 :: c :: r =>
      match class_esc c with
      | Some ci => Some (R_Set false [ci], r, g)
      | None =>
        if (49 <=? c) && (c <=? 57) then
          (if flav_backref fl then Some (R_Back (Z.to_nat (c - 48)), r, g) else None)
        else if c =? 65 then Some (R_Start, r, g)
        else if (c =? 122) || (c =? 90) then Some (R_End, r, g)
        else if flav_pg fl then
          (if c =? 121 then Some (R_WordB true, r, g) else if c =? 89 then Some (R_WordB false, r, g)
           else if c =? 109 then Some (R_WordStart, r, g) else if c =? 77 then Some (R_WordEnd, r, g)
           else if c =? 98 then Some (R_Char 8, r, g)
           else Some (R_Char (char_esc c), r, g))
        else if c =? 98 then Some (R_WordB true, r, g) else if c =? 66 then Some (R_WordB false, r, g)
        else Some (R_Char (char_esc c), r, g)
      end
    | 92 :: nil => None
    | 42 :: _ | 43 :: _ | 63 :: _ => None   (* a quantifier without operand *)
    | c :: r => Some (R_Char c, r, g)
    | nil => None
    end
  end.

End Parse.

(** the expression of a pattern; [None] if it is not well formed *)
Definition parse_re (fl : flavor) (p : list Z) : option re :=
  match p_alt fl (4 * S (List.length p)) p 0 with
  | Some (r, nil, _) => Some r
  | _ => None
  end.

Definition fl_pg := mk_flavor true true true.
Definition fl_icu := mk_flavor false true true.      (* MySQL 8, OceanBase MySQL mode *)
Definition fl_pcre := mk_flavor false true true.     (* MariaDB *)
Definition fl_re2 := mk_flavor false false false.    (* TiDB: Go's regexp *)
Definition fl_ora := mk_flavor false true false.     (* Oracle *)

(** * Replacement

    [repl] is read as a template: [\n] (PostgreSQL, Oracle, MariaDB) or [$n] (ICU) is the [n]-th group,
    [\&] (PostgreSQL) the whole match; [\\] is a backslash. *)
Definition group_text (s : list Z) (x : rmatch) (n : nat) : list Z :=
  let '(b, e, cs) := x in
  match n with
  | O => firstn (e - b) (skipn b s)
  | S k => match nth_error cs k with
           | Some (Some (gb, ge)) => firstn (ge - gb) (skipn gb s)
           | _ => nil
           end
  end.

Fixpoint expand (dollar : bool) (s : list Z) (x : rmatch) (t : list Z) : list Z :=
  match t with
  | nil => nil
  | 92 :: 92 :: r => 92 :: expand dollar s x r
  | 92 :: 38 :: r => if dollar then 38 :: expand dollar s x r else group_text s x 0 ++ expand dollar s x r
  | 92 :: c :: r => if negb dollar && (48 <=? c) && (c <=? 57) then group_text s x (Z.to_nat (c - 48)) ++ expand dollar s x r
                    else if dollar then c :: expand dollar s x r else 92 :: c :: expand dollar s x r
  | 36 :: r => match r with
               | c :: r' => if dollar && (48 <=? c) && (c <=? 57) then group_text s x (Z.to_nat (c - 48)) ++ expand dollar s x r'
                            else 36 :: expand dollar s x r
               | nil => 36 :: nil
               end
  | c :: r => c :: expand dollar s x r
  end.

(** replace the matches [ms] (in order, without overlap) of [s] *)
Fixpoint replace_matches (dollar : bool) (s : list Z) (t : list Z) (ms : list rmatch) (i : nat) : list Z :=
  match ms with
  | nil => skipn i s
  | ((b, e, _) as x) :: r => firstn (b - i) (skipn i s) ++ expand dollar s x t ++ replace_matches dollar s t r e
  end.
