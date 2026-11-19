(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   The functions of regular expressions of each dialect (TODO 2.4).              *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String Ascii ZArith Bool.

Require Import Bool3 Values ValueKit StringFuns Regex.

Import ListNotations.
Import NullValues.
Open Scope Z_scope.
Open Scope bool_scope.

(** A dialect's regular expressions: its argument conversions, the syntax, PostgreSQL's choice of the
    match ([rx_pg]) or the leftmost-first one, the default options, the syntax of the replacement
    ([rx_dollar]: [$n], else [\n]), and the message of an invalid expression. *)
Record rx_env : Type := mk_rx_env
  { rx_k : skit;
    rx_fl : flavor;
    rx_pg : bool;
    rx_icase : bool;
    rx_dotnl : bool;
    rx_dollar : bool;
    rx_err : string }.

Definition rx_policy (e : rx_env) (r : re) : policy := if rx_pg e then pg_policy r else Leftmost_First.

(** the flags: [i] case-insensitive, [c] case-sensitive, [m] multi-line, [n] (MySQL, Oracle) [.] matches a
    line break, [n] (PostgreSQL) newline-sensitive, [s] (PostgreSQL) not, [g] (PostgreSQL) all the
    matches, [u] and [x] (ignored: [x] is not modelled, an error); the result is the options and [g] *)
Fixpoint rx_flags (e : rx_env) (l : list Z) (o : ropts) (g : bool) : option (ropts * bool) :=
  match l with
  | nil => Some (o, g)
  | c :: r =>
    let o' := if c =? 105 then Some (mk_ropts true (o_multiline o) (o_dotnl o))
              else if c =? 99 then Some (mk_ropts false (o_multiline o) (o_dotnl o))
              else if c =? 109 then Some (mk_ropts (o_icase o) true (o_dotnl o))
              else if c =? 110 then Some (if rx_pg e then mk_ropts (o_icase o) true false else mk_ropts (o_icase o) (o_multiline o) true)
              else if (c =? 115) && rx_pg e then Some (mk_ropts (o_icase o) false true)
              else if (c =? 103) && rx_pg e then Some o
              else if c =? 117 then Some o
              else None in
    match o' with Some o' => rx_flags e r o' (g || (c =? 103)) | None => None end
  end.

Definition rx_default (e : rx_env) : ropts := mk_ropts (rx_icase e) false (rx_dotnl e).

(** the text, the expression and the options; [None] is a NULL argument, [Some None] an error *)
Definition rx_setup (e : rx_env) (s p : value) (flags : option value) : option (option (list Z * re * ropts * bool)) :=
  let k := rx_k e in
  match sk_txt k s, sk_txt k p, match flags with Some f => option_map Some (sk_txt k f) | None => Some None end with
  | Some s, Some p, Some fl =>
    match parse_re (rx_fl e) (cps p),
          rx_flags e (match fl with Some f => cps f | None => nil end) (rx_default e) false with
    | Some r, Some (o, g) => Some (Some (cps s, r, o, g))
    | _, _ => Some None
    end
  | _, _, _ => None
  end.

(** the optional integer argument [n] of [l] (1-based), [d] by default; [None] if it is NULL *)
Definition opt_int (e : rx_env) (l : list value) (n : nat) (d : Z) : option Z :=
  match nth_error l n with Some v => sk_int (rx_k e) v | None => Some d end.

Definition opt_val (l : list value) (n : nat) : option value := nth_error l n.

(** [s ~ p] and [REGEXP_LIKE (s, p [, flags])] *)
Definition rx_like (e : rx_env) (icase : bool) (l : list value) : bool3 :=
  match l with
  | s :: p :: rest =>
    let e := mk_rx_env (rx_k e) (rx_fl e) (rx_pg e) (icase || rx_icase e) (rx_dotnl e) (rx_dollar e) (rx_err e) in
    match rx_setup e s p (opt_val rest 0) with
    | Some (Some (s, r, o, _)) => bool3_of_bool (match search o (rx_policy e r) r s 0 with Some _ => true | None => false end)
    | _ => unknown3
    end
  | _ => unknown3
  end.

(** an invalid expression or flag in a predicate ([pred_error]) *)
Definition rx_bad (e : rx_env) (names : list string) (p : string) (l : list value) : bool :=
  existsb (String.eqb p) names &&
  match l with
  | s :: q :: rest => match rx_setup e s q (opt_val rest 0) with Some None => true | _ => false end
  | _ => false
  end.

Definition with_setup (e : rx_env) (null : value) (s p : value) (flags : option value)
           (f : list Z -> re -> ropts -> bool -> value) : value :=
  match rx_setup e s p flags with
  | Some (Some (s, r, o, g)) => f s r o g
  | Some None => Value_Err (rx_err e)
  | None => null
  end.

(** the matches from the position [pos] (1-based) *)
Definition from_pos (e : rx_env) (s : list Z) (r : re) (o : ropts) (pos : Z) : list rmatch :=
  matches o (rx_policy e r) r s (Z.to_nat (pos - 1)).

(** [REGEXP_COUNT (s, p [, pos [, flags]])] *)
Definition rx_count (e : rx_env) (l : list value) : value :=
  match l with
  | s :: p :: rest =>
    match opt_int e rest 0 1 with
    | Some pos => with_setup e (Value_Z None) s p (opt_val rest 1)
                    (fun s r o _ => if pos <? 1 then Value_Err (rx_err e)
                                    else Value_Z (Some (Z.of_nat (List.length (from_pos e s r o pos)))))
    | None => Value_Z None
    end
  | _ => Value_Err "wrong number of arguments"
  end.

(** [REGEXP_INSTR (s, p [, pos [, occurrence [, return_option [, flags [, group]]]]])]: the position (1-based)
    of the start (or, with [return_option] 1, of the end) of the [occurrence]-th match, 0 if none *)
Definition rx_instr (e : rx_env) (l : list value) : value :=
  match l with
  | s :: p :: rest =>
    match opt_int e rest 0 1, opt_int e rest 1 1, opt_int e rest 2 0, opt_int e rest 4 0 with
    | Some pos, Some occ, Some ret, Some grp =>
      with_setup e (Value_Z None) s p (opt_val rest 3)
        (fun s r o _ =>
           if (pos <? 1) || (occ <? 1) then Value_Err (rx_err e)
           else match nth_error (from_pos e s r o pos) (Z.to_nat (occ - 1)) with
                | Some ((b, en, cs) as x) =>
                  let '(gb, ge) := match grp with
                                   | 0 => (b, en)
                                   | _ => match nth_error cs (Z.to_nat (grp - 1)) with
                                          | Some (Some be) => be | _ => (O, O) end
                                   end in
                  if (0 <? grp) && Nat.eqb gb 0 && Nat.eqb ge 0 && negb (Nat.eqb b 0) then Value_Z (Some 0)
                  else Value_Z (Some (Z.of_nat (if ret =? 0 then gb else ge) + 1))
                | None => Value_Z (Some 0)
                end)
    | _, _, _, _ => Value_Z None
    end
  | _ => Value_Err "wrong number of arguments"
  end.

(** [REGEXP_SUBSTR (s, p [, pos [, occurrence [, flags [, group]]]])]: NULL if there is no match *)
Definition rx_substr (e : rx_env) (l : list value) : value :=
  match l with
  | s :: p :: rest =>
    match opt_int e rest 0 1, opt_int e rest 1 1, opt_int e rest 3 0 with
    | Some pos, Some occ, Some grp =>
      with_setup e (sk_null (rx_k e)) s p (opt_val rest 2)
        (fun s r o _ =>
           if (pos <? 1) || (occ <? 1) then Value_Err (rx_err e)
           else match nth_error (from_pos e s r o pos) (Z.to_nat (occ - 1)) with
                | Some x => ret_cp (rx_k e) (group_text s x (Z.to_nat grp))
                | None => sk_null (rx_k e)
                end)
    | _, _, _ => sk_null (rx_k e)
    end
  | _ => Value_Err "wrong number of arguments"
  end.

(** [REGEXP_REPLACE (s, p, t [, pos [, occurrence [, flags]]])]: the [occurrence]-th match, all of them
    if it is 0 (the default when [all]); PostgreSQL replaces the first one unless the flag [g] *)
Definition rx_replace_gen (e : rx_env) (all : bool) (s p t : value) (pos occ : option Z) (flags : option value) : value :=
  match sk_txt (rx_k e) t, pos, occ with
  | Some t, Some pos, Some occ =>
    with_setup e (sk_null (rx_k e)) s p flags
      (fun s r o g =>
         if (pos <? 1) || (occ <? 0) then Value_Err (rx_err e)
         else let ms := from_pos e s r o pos in
              let chosen := if (occ =? 0) && (all || g) then ms
                            else if occ =? 0 then firstn 1 ms
                            else match nth_error ms (Z.to_nat (occ - 1)) with Some x => [x] | None => nil end in
              ret_cp (rx_k e) (replace_matches (rx_dollar e) s (cps t) chosen 0))
  | _, _, _ => sk_null (rx_k e)
  end.

(** the MySQL and Oracle form: [REGEXP_REPLACE (s, p, t [, pos [, occurrence [, flags]]])], all by default *)
Definition rx_replace (e : rx_env) (l : list value) : value :=
  match l with
  | s :: p :: t :: rest => rx_replace_gen e true s p t (opt_int e rest 0 1) (opt_int e rest 1 0) (opt_val rest 2)
  | s :: p :: nil => rx_replace_gen e true s p (Value_string (Some EmptyString)) (Some 1) (Some 0) None
  | _ => Value_Err "wrong number of arguments"
  end.

(** PostgreSQL: [regexp_replace (s, p, t [, flags])] or [regexp_replace (s, p, t, start [, N [, flags]])] *)
Definition pg_regexp_replace (e : rx_env) (l : list value) : value :=
  match l with
  | s :: p :: t :: nil => rx_replace_gen e false s p t (Some 1) (Some 0) None
  | s :: p :: t :: ((Value_string _ | Value_C _) as f) :: nil => rx_replace_gen e false s p t (Some 1) (Some 0) (Some f)
  | s :: p :: t :: rest => rx_replace_gen e false s p t (opt_int e rest 0 1) (opt_int e rest 1 0) (opt_val rest 2)
  | _ => Value_Err "wrong number of arguments"
  end.

(** PostgreSQL [substring (s from pattern)]: the text of the first group if there is one, else of the match *)
Definition pg_substring_regex (e : rx_env) (l : list value) : value :=
  match l with
  | s :: p :: nil =>
    with_setup e (Value_string None) s p None
      (fun s r o _ => match search o (rx_policy e r) r s 0 with
                      | Some x => if Nat.eqb (ngroups r) 0 then ret_cp (rx_k e) (group_text s x 0)
                                  else match x with
                                       | (_, _, Some _ :: _) => ret_cp (rx_k e) (group_text s x 1)
                                       | _ => Value_string None end
                      | None => Value_string None
                      end)
  | _ => Value_Err "wrong number of arguments"
  end.

(** [SIMILAR TO]: the SQL pattern as an anchored ARE: [%] is [.*], [_] is [.], the escape character
    (default [\]) quotes the next one; the other ARE operators keep their meaning ([similar_to_escape]) *)
Fixpoint similar_aux (esc : option Z) (l : list Z) (in_br : bool) : list Z :=
  match l with
  | nil => nil
  | c :: r =>
    if (match esc with Some x => c =? x | None => false end) then
      match r with d :: r' => 92 :: d :: similar_aux esc r' in_br | nil => [92; 92] end
    else if in_br then (if c =? 93 then 93 :: similar_aux esc r false else c :: similar_aux esc r true)
    else if c =? 37 then 46 :: 42 :: similar_aux esc r false
    else if c =? 95 then 46 :: similar_aux esc r false
    else if c =? 91 then 91 :: similar_aux esc r true
    else if (c =? 46) || (c =? 94) || (c =? 36) then 92 :: c :: similar_aux esc r false
    else c :: similar_aux esc r false
  end.

Definition similar_to_re (esc : option Z) (p : list Z) : list Z :=
  [94; 40; 63; 58] ++ similar_aux esc p false ++ [41; 36].

Definition pg_similar (e : rx_env) (l : list value) : bool3 :=
  match l with
  | s :: p :: rest =>
    let esc := match rest with
               | v :: nil => match sk_txt (rx_k e) v with Some x => match cps x with c :: _ => Some c | nil => None end | None => None end
               | _ => Some 92 end in
    match sk_txt (rx_k e) p with
    | Some p => rx_like e false [s; Value_string (Some (txt (similar_to_re esc (cps p))))]
    | None => unknown3
    end
  | _ => unknown3
  end.
