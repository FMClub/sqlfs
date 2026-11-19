(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   JSON: values, parsing, the texts of the engines, paths.                       *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String Ascii ZArith Bool.

Import ListNotations.
Open Scope string_scope.

(** * Values

    A number keeps its text ([1.50] stays [1.50] in a PostgreSQL [jsonb]); objects keep the order of
    their members, the engines which sort them do it when they build a value ([normalize]). *)
Inductive json : Type :=
  | JNull : json
  | JBool : bool -> json
  | JNum : string -> json
  | JStr : string -> json
  | JArr : list json -> json
  | JObj : list (string * json) -> json.

(** * Parsing (RFC 8259); [None] for an invalid text *)
Definition is_space (c : ascii) : bool :=
  match c with " " | "010" | "013" | "009" => true | _ => false end%char.

Fixpoint skip_ws (s : string) : string :=
  match s with String c r => if is_space c then skip_ws r else s | EmptyString => s end.

Definition is_num_char (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (Nat.leb 48 n && Nat.leb n 57) || match c with "-" | "+" | "." | "e" | "E" => true | _ => false end%char.

Fixpoint take_num (s : string) : string * string :=
  match s with
  | String c r => if is_num_char c then let (a, b) := take_num r in (String c a, b) else (EmptyString, s)
  | EmptyString => (EmptyString, EmptyString)
  end.

(** a string literal, after its opening quote: the content (the escapes of a backslash resolved for the
    quote, the backslash, the slash, n, t, r, b, f) and the rest *)
Fixpoint take_str (fuel : nat) (s : string) : option (string * string) :=
  match fuel with
  | O => None
  | S f =>
    match s with
    | EmptyString => None
    | String "\" (String c r) =>
      let c' := match c with "n" => "010" | "t" => "009" | "r" => "013" | "b" => "008" | "f" => "012" | _ => c end%char in
      match take_str f r with Some (a, b) => Some (String c' a, b) | None => None end
    | String c r =>
      if Ascii.eqb c """" then Some (EmptyString, r)
      else match take_str f r with Some (a, b) => Some (String c a, b) | None => None end
    end
  end.

Definition valid_number (t : string) : bool :=
  match t with
  | EmptyString => false
  | String c _ => negb (Ascii.eqb c "+") && negb (Ascii.eqb c ".")
  end.

Fixpoint parse_value (fuel : nat) (s : string) : option (json * string) :=
  match fuel with
  | O => None
  | S f =>
    let s := skip_ws s in
    if String.prefix "null" s then Some (JNull, substring 4 (String.length s - 4) s)
    else if String.prefix "true" s then Some (JBool true, substring 4 (String.length s - 4) s)
    else if String.prefix "false" s then Some (JBool false, substring 5 (String.length s - 5) s)
    else match s with
         | String c r =>
           if Ascii.eqb c """" then
             match take_str (String.length r) r with Some (a, b) => Some (JStr a, b) | None => None end
           else if Ascii.eqb c "[" then
             let r := skip_ws r in
             match r with
             | String "]" r' => Some (JArr nil, r')
             | _ =>
               (fix items (g : nat) (t : string) (acc : list json) : option (json * string) :=
                  match g with
                  | O => None
                  | S g =>
                    match parse_value f t with
                    | Some (v, t) =>
                      match skip_ws t with
                      | String "," t => items g t (app acc [v])
                      | String "]" t => Some (JArr (app acc [v]), t)
                      | _ => None
                      end
                    | None => None
                    end
                  end) f r nil
             end
           else if Ascii.eqb c "{" then
             let r := skip_ws r in
             match r with
             | String "}" r' => Some (JObj nil, r')
             | _ =>
               (fix members (g : nat) (t : string) (acc : list (string * json)) : option (json * string) :=
                  match g with
                  | O => None
                  | S g =>
                    match skip_ws t with
                    | String q t =>
                      if Ascii.eqb q """" then
                        match take_str (String.length t) t with
                        | Some (k, t) =>
                          match skip_ws t with
                          | String ":" t =>
                            match parse_value f t with
                            | Some (v, t) =>
                              match skip_ws t with
                              | String "," t => members g t (app acc [(k, v)])
                              | String "}" t => Some (JObj (app acc [(k, v)]), t)
                              | _ => None
                              end
                            | None => None
                            end
                          | _ => None
                          end
                        | None => None
                        end
                      else None
                    | EmptyString => None
                    end
                  end) f r nil
             end
           else let (t, rest) := take_num s in if valid_number t then Some (JNum t, rest) else None
         | EmptyString => None
         end
  end.

Definition parse_json (s : string) : option json :=
  match parse_value (S (String.length s)) s with
  | Some (v, rest) => match skip_ws rest with EmptyString => Some v | _ => None end
  | None => None
  end.

(** * Normalization

    MySQL ([Json_object], [json_binary]) and PostgreSQL [jsonb] ([uniqueifyJsonbObject]) sort the members of
    an object by the length of the key, then by its bytes, and keep only the last value of a duplicated
    key; SQLite keeps the text, and the order of the members. *)
Definition key_lt (a b : string) : bool :=
  Nat.ltb (String.length a) (String.length b) ||
  (Nat.eqb (String.length a) (String.length b) && match String.compare a b with Lt => true | _ => false end).

Fixpoint insert_member (m : string * json) (l : list (string * json)) : list (string * json) :=
  match l with
  | nil => [m]
  | x :: r => if String.eqb (fst m) (fst x) then m :: r
              else if key_lt (fst m) (fst x) then m :: l else x :: insert_member m r
  end.

Fixpoint normalize (j : json) : json :=
  match j with
  | JArr l => JArr (map normalize l)
  | JObj l => JObj (fold_left (fun acc m => insert_member (fst m, normalize (snd m)) acc) l nil)
  | _ => j
  end.

(** * Texts *)
Fixpoint escape (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c r =>
    let e := if Ascii.eqb c """" then "\"""
             else if Ascii.eqb c "\" then "\\"
             else if Ascii.eqb c "010" then "\n"
             else if Ascii.eqb c "009" then "\t"
             else if Ascii.eqb c "013" then "\r"
             else String c EmptyString in
    e ++ escape r
  end.

(** [sep_item] after a comma, [sep_key] after a colon: MySQL and PostgreSQL write a space after them,
    SQLite does not *)
Fixpoint json_text (sep_item sep_key : string) (j : json) : string :=
  match j with
  | JNull => "null"
  | JBool b => if b then "true" else "false"
  | JNum t => t
  | JStr s => """" ++ escape s ++ """"
  | JArr l => "[" ++ (fix go (l : list json) : string :=
                        match l with
                        | nil => ""
                        | [x] => json_text sep_item sep_key x
                        | x :: r => json_text sep_item sep_key x ++ "," ++ sep_item ++ go r
                        end) l ++ "]"
  | JObj l => "{" ++ (fix go (l : list (string * json)) : string :=
                        match l with
                        | nil => ""
                        | [(k, v)] => """" ++ escape k ++ """:" ++ sep_key ++ json_text sep_item sep_key v
                        | (k, v) :: r => """" ++ escape k ++ """:" ++ sep_key ++ json_text sep_item sep_key v ++ "," ++ sep_item ++ go r
                        end) l ++ "}"
  end.

Definition text_spaced (j : json) : string := json_text " " " " j.
Definition text_compact (j : json) : string := json_text "" "" j.

(** * Paths

    A path is a list of steps: a member of an object or an element of an array (from the end for a
    negative index, as SQLite's [#-n]). *)
Inductive step : Type := SKey : string -> step | SIdx : Z -> step.

Fixpoint follow (p : list step) (j : json) : option json :=
  match p with
  | nil => Some j
  | SKey k :: r => match j with
                   | JObj l => match find (fun m => String.eqb (fst m) k) (rev l) with Some (_, v) => follow r v | None => None end
                   | _ => None
                   end
  | SIdx i :: r => match j with
                   | JArr l => let n := Z.of_nat (List.length l) in
                               let i := if Z.ltb i 0 then (n + i)%Z else i in
                               if (Z.leb 0 i && Z.ltb i n)%bool then match nth_error l (Z.to_nat i) with Some v => follow r v | None => None end
                               else None
                   | _ => None
                   end
  end.

Definition digits_value (s : string) : option Z :=
  match s with
  | EmptyString => None
  | _ => fold_left (fun acc c => match acc with
                                 | Some v => let n := Z.of_nat (nat_of_ascii c) in
                                             if (Z.leb 48 n && Z.leb n 57)%bool then Some (v * 10 + (n - 48))%Z else None
                                 | None => None end) (list_ascii_of_string s) (Some 0%Z)
  end.

(** the path language of MySQL and SQLite: [$], [.key], [."key"], [[n]], and SQLite's [[#-n]];
    the wildcards are not modelled (an invalid path) *)
Fixpoint parse_path_steps (fuel : nat) (s : string) : option (list step) :=
  match fuel with
  | O => None
  | S f =>
    match s with
    | EmptyString => Some nil
    | String "." (String """" r) =>
      match take_str (String.length r) r with
      | Some (k, rest) => match parse_path_steps f rest with Some p => Some (SKey k :: p) | None => None end
      | None => None
      end
    | String "." r =>
      let k := (fix key (t : string) : string :=
                  match t with
                  | String c t' => if (Ascii.eqb c "." || Ascii.eqb c "[")%bool then EmptyString else String c (key t')
                  | EmptyString => EmptyString end) r in
      if String.eqb k EmptyString then None else
      match parse_path_steps f (substring (String.length k) (String.length r - String.length k) r) with
      | Some p => Some (SKey k :: p) | None => None end
    | String "[" r =>
      let inside := (fix upto (t : string) : string := match t with String "]" _ => EmptyString | String c t' => String c (upto t') | EmptyString => EmptyString end) r in
      let rest := substring (S (String.length inside)) (String.length r - S (String.length inside)) r in
      let idx := match inside with
                 | String "#" (String "-" n) => match digits_value n with Some v => Some (Z.opp v) | None => None end
                 | _ => digits_value inside
                 end in
      match idx with
      | Some i => match parse_path_steps f rest with Some p => Some (SIdx i :: p) | None => None end
      | None => None
      end
    | _ => None
    end
  end.

Definition parse_path (s : string) : option (list step) :=
  match s with
  | String "$" r => parse_path_steps (S (String.length r)) r
  | _ => None
  end.

(** * Types and lengths *)
Definition json_type_name (j : json) : string :=
  match j with
  | JNull => "NULL" | JBool _ => "BOOLEAN" | JNum t => if existsb (fun c => (Ascii.eqb c "." || Ascii.eqb c "e" || Ascii.eqb c "E")%bool) (list_ascii_of_string t) then "DOUBLE" else "INTEGER"
  | JStr _ => "STRING" | JArr _ => "ARRAY" | JObj _ => "OBJECT"
  end.

Definition json_length (j : json) : Z :=
  match j with JArr l => Z.of_nat (List.length l) | JObj l => Z.of_nat (List.length l) | _ => 1%Z end.

(** [JSON_CONTAINS] / [@>]: an object contains an object whose members it contains, an array contains the
    elements (or the scalars) it contains, a scalar contains an equal scalar *)
Fixpoint json_contains (fuel : nat) (a b : json) : bool :=
  match fuel with
  | O => false
  | S f =>
    match a, b with
    | JObj la, JObj lb => forallb (fun m => match find (fun x => String.eqb (fst x) (fst m)) la with
                                            | Some (_, v) => json_contains f v (snd m) | None => false end) lb
    | JArr la, JArr lb => forallb (fun y => existsb (fun x => json_contains f x y) la) lb
    | JArr la, _ => existsb (fun x => json_contains f x b) la
    | JNum x, JNum y => String.eqb x y
    | JStr x, JStr y => String.eqb x y
    | JBool x, JBool y => Bool.eqb x y
    | JNull, JNull => true
    | _, _ => false
    end
  end.

Fixpoint json_size (j : json) : nat :=
  match j with
  | JArr l => S (fold_left (fun acc x => acc + json_size x) l 0)
  | JObj l => S (fold_left (fun acc m => acc + json_size (snd m)) l 0)
  | _ => 1
  end.

Definition normalize_members (l : list (string * json)) : list (string * json) :=
  match normalize (JObj l) with JObj l' => l' | _ => l end.
