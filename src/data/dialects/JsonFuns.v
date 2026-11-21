(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   JSON functions (TODO 2.8): updates by path, removal, arrays, merges, depth,   *)
(**   search, pretty printing, the [jsonb] operators of PostgreSQL.                 *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String Ascii ZArith Bool.

Require Import Json.

Import ListNotations.
Open Scope bool_scope.

(** * Updates by path (MySQL [JSON_SET], [JSON_INSERT], [JSON_REPLACE]; SQLite [json_set], ...)

    [create]: a missing last member or element is added (at the end of an array, whatever the index);
    [replace]: an existing one is replaced. A step [[0]] on a value which is not an array designates the
    value itself, and a larger index wraps it in an array ([JSON_SET('1', '$[1]', 2)] is [[1, 2]]). *)
Fixpoint set_path (create replace : bool) (p : list step) (j v : json) : json :=
  match p with
  | nil => if replace then v else j
  | SKey k :: r =>
    match j with
    | JObj ms =>
      if existsb (fun m => String.eqb (fst m) k) ms
      then JObj (map (fun m => if String.eqb (fst m) k then (fst m, set_path create replace r (snd m) v) else m) ms)
      else match r with nil => if create then JObj (ms ++ [(k, v)]) else j | _ => j end
    | _ => j
    end
  | SIdx i :: r =>
    match j with
    | JArr l =>
      let n := Z.of_nat (List.length l) in
      let i := if Z.ltb i 0 then (n + i)%Z else i in
      if Z.leb 0 i && Z.ltb i n
      then JArr (firstn (Z.to_nat i) l ++ [set_path create replace r (nth (Z.to_nat i) l JNull) v] ++ skipn (S (Z.to_nat i)) l)
      else match r with nil => if create && Z.leb n i then JArr (l ++ [v]) else j | _ => j end
    | _ => if Z.eqb i 0 || Z.eqb i (-1) then set_path create replace r j v   (* [[0]], [[last]] *)
           else match r with nil => if create && Z.ltb 0 i then JArr [j; v] else j | _ => j end
    end
  end.

(** [JSON_REMOVE] / [json_remove]: the member or the element at the path, if there is one *)
Fixpoint remove_path (p : list step) (j : json) : json :=
  match p with
  | nil => j
  | SKey k :: nil => match j with JObj ms => JObj (filter (fun m => negb (String.eqb (fst m) k)) ms) | _ => j end
  | SIdx i :: nil => match j with
                     | JArr l => let n := Z.of_nat (List.length l) in
                                 let i := if Z.ltb i 0 then (n + i)%Z else i in
                                 if Z.leb 0 i && Z.ltb i n then JArr (firstn (Z.to_nat i) l ++ skipn (S (Z.to_nat i)) l) else j
                     | _ => j end
  | SKey k :: r => match j with JObj ms => JObj (map (fun m => if String.eqb (fst m) k then (fst m, remove_path r (snd m)) else m) ms) | _ => j end
  | SIdx i :: r => match j with
                   | JArr l => let n := Z.of_nat (List.length l) in
                               let i := if Z.ltb i 0 then (n + i)%Z else i in
                               JArr (map (fun p => if Z.eqb (Z.of_nat (fst p)) i then remove_path r (snd p) else snd p) (combine (seq 0 (List.length l)) l))
                   | _ => j end
  end.

(** apply [f] to the value at the path *)
Fixpoint at_path (f : json -> json) (p : list step) (j : json) : json :=
  match p with
  | nil => f j
  | SKey k :: r => match j with JObj ms => JObj (map (fun m => if String.eqb (fst m) k then (fst m, at_path f r (snd m)) else m) ms) | _ => j end
  | SIdx i :: r => match j with
                   | JArr l => let n := Z.of_nat (List.length l) in
                               let i := if Z.ltb i 0 then (n + i)%Z else i in
                               JArr (map (fun q => if Z.eqb (Z.of_nat (fst q)) i then at_path f r (snd q) else snd q) (combine (seq 0 (List.length l)) l))
                   | _ => if Z.eqb i 0 then at_path f r j else j end
  end.

(** [JSON_ARRAY_APPEND]: the value is added at the end of the array at the path; a value which is not an
    array is first wrapped in one *)
Definition array_append (p : list step) (j v : json) : json :=
  at_path (fun t => match t with JArr l => JArr (l ++ [v]) | _ => JArr [t; v] end) p j.

(** [JSON_ARRAY_INSERT]: the path ends with an index; the value is inserted there (at the end beyond it) *)
Definition array_insert (p : list step) (j v : json) : option json :=
  match rev p with
  | SIdx i :: rp => Some (at_path (fun t => match t with
                                            | JArr l => let k := Z.to_nat (Z.max 0 i) in JArr (firstn k l ++ [v] ++ skipn k l)
                                            | _ => t end) (rev rp) j)
  | _ => None
  end.

(** [JSON_MERGE_PATCH] / [json_patch] (RFC 7396): the members of an object patch replace or (with [null])
    remove those of the target; a patch which is not an object replaces the target *)
Fixpoint merge_patch (fuel : nat) (t p : json) : json :=
  match fuel with
  | O => p
  | S f =>
    match p with
    | JObj pm =>
      let tm := match t with JObj l => l | _ => nil end in
      let kept := filter (fun m => negb (existsb (fun x => String.eqb (fst x) (fst m)) pm)) tm in
      let upd := flat_map (fun m => match snd m with
                                    | JNull => nil
                                    | v => [(fst m, merge_patch f (match find (fun x => String.eqb (fst x) (fst m)) tm with
                                                                   | Some (_, old) => old | None => JNull end) v)]
                                    end) pm in
      (* the order of the target's members, then the new ones *)
      let merged := map (fun m => match find (fun x => String.eqb (fst x) (fst m)) upd with Some u => u | None => m end)
                        (filter (fun m => existsb (fun x => String.eqb (fst x) (fst m)) upd || existsb (fun x => String.eqb (fst x) (fst m)) kept) tm) in
      let added := filter (fun u => negb (existsb (fun m => String.eqb (fst m) (fst u)) tm)) upd in
      JObj (merged ++ added)
    | _ => p
    end
  end.

(** [JSON_MERGE_PRESERVE]: arrays are concatenated, a scalar is wrapped in an array, objects are merged
    member by member, two values for one key being merged *)
Fixpoint merge_preserve (fuel : nat) (a b : json) : json :=
  match fuel with
  | O => b
  | S f =>
    match a, b with
    | JObj la, JObj lb =>
      JObj (map (fun m => match find (fun x => String.eqb (fst x) (fst m)) lb with
                          | Some (_, v) => (fst m, merge_preserve f (snd m) v) | None => m end) la
            ++ filter (fun m => negb (existsb (fun x => String.eqb (fst x) (fst m)) la)) lb)
    | JArr la, JArr lb => JArr (la ++ lb)
    | JArr la, _ => JArr (la ++ [b])
    | _, JArr lb => JArr (a :: lb)
    | _, _ => JArr [a; b]
    end
  end.

(** [JSON_DEPTH]: 1 for a scalar or an empty container *)
Fixpoint json_depth_aux (fuel : nat) (j : json) : nat :=
  match fuel with
  | O => 1
  | S f =>
    match j with
    | JArr ((_ :: _) as l) => S (fold_left Nat.max (map (json_depth_aux f) l) 0)
    | JObj ((_ :: _) as l) => S (fold_left Nat.max (map (fun m => json_depth_aux f (snd m)) l) 0)
    | _ => 1
    end
  end.
Definition json_depth (j : json) : nat := json_depth_aux (json_size j) j.

(** [JSON_SEARCH (doc, 'one' | 'all', s)]: the paths of the strings equal to [s] (the [LIKE] wildcards are
    not modelled), in document order *)
Fixpoint text_of_nat_aux (fuel : nat) (k : nat) (acc : string) : string :=
  match fuel with
  | O => acc
  | S f => let d := String (ascii_of_nat (48 + Nat.modulo k 10)) EmptyString in
           if Nat.ltb k 10 then (d ++ acc)%string else text_of_nat_aux f (Nat.div k 10) (d ++ acc)%string
  end.
Definition text_of_nat (n : nat) : string := text_of_nat_aux 20 n EmptyString.

Fixpoint search_paths (fuel : nat) (s : string) (prefix : string) (j : json) : list string :=
  match fuel with
  | O => nil
  | S f =>
    match j with
    | JStr t => if String.eqb t s then [prefix] else nil
    | JArr l => List.concat (map (fun p => search_paths f s (prefix ++ "[" ++ text_of_nat (fst p) ++ "]") (snd p))
                                 (combine (seq 0 (List.length l)) l))
    | JObj l => List.concat (map (fun m => search_paths f s (prefix ++ "." ++ fst m) (snd m)) l)
    | _ => nil
    end
  end.

(** [JSON_OVERLAPS]: two arrays share an element, two objects a member, or two scalars are equal *)
Definition json_overlaps (a b : json) : bool :=
  let eqj x y := String.eqb (text_compact (normalize x)) (text_compact (normalize y)) in
  match a, b with
  | JArr la, JArr lb => existsb (fun x => existsb (eqj x) lb) la
  | JArr la, _ => existsb (fun x => eqj x b) la
  | _, JArr lb => existsb (eqj a) lb
  | JObj la, JObj lb => existsb (fun m => existsb (fun x => String.eqb (fst x) (fst m) && eqj (snd x) (snd m)) lb) la
  | _, _ => eqj a b
  end.

(** * Pretty printing: [JSON_PRETTY] (2 spaces) and [jsonb_pretty] (4 spaces), one member or element per line *)
Fixpoint spaces (n : nat) : string := match n with O => EmptyString | S k => String " " (spaces k) end.

Fixpoint pretty_aux (fuel : nat) (ind : nat) (lvl : nat) (j : json) : string :=
  let nl := String (ascii_of_nat 10) EmptyString in
  match fuel with
  | O => text_spaced j
  | S f =>
    match j with
    | JArr ((_ :: _) as l) =>
      "[" ++ nl ++ String.concat ("," ++ nl) (map (fun x => spaces (ind * S lvl) ++ pretty_aux f ind (S lvl) x) l) ++ nl ++ spaces (ind * lvl) ++ "]"
    | JObj ((_ :: _) as l) =>
      "{" ++ nl ++ String.concat ("," ++ nl) (map (fun m => spaces (ind * S lvl) ++ text_compact (JStr (fst m)) ++ ": " ++ pretty_aux f ind (S lvl) (snd m)) l)
          ++ nl ++ spaces (ind * lvl) ++ "}"
    | _ => text_spaced j
    end
  end.
Definition pretty (ind : nat) (j : json) : string := pretty_aux (json_size j) ind 0 j.

(** * PostgreSQL

    A path of [jsonb_set], [#>], [#-] is a text array ['{a,0,b}']: an element designates a member of an
    object, or (an integer) an element of an array. *)
Fixpoint split_commas (l : list ascii) (cur : list ascii) : list string :=
  match l with
  | nil => [string_of_list_ascii (rev cur)]
  | c :: r => if Ascii.eqb c ","%char then string_of_list_ascii (rev cur) :: split_commas r nil else split_commas r (c :: cur)
  end.

Definition pg_text_array (s : string) : option (list string) :=
  match list_ascii_of_string s with
  | "{"%char :: r => match rev r with
                     | "}"%char :: inner => match inner with nil => Some nil | _ => Some (split_commas (rev inner) nil) end
                     | _ => None end
  | _ => None
  end.

(** a text step: a member of an object, an index of an array *)
Definition int_of_text (t : string) : option Z :=
  match t with
  | String "-" r => option_map Z.opp (digits_value r)
  | _ => digits_value t
  end.

Fixpoint pg_set (create : bool) (p : list string) (j v : json) : json :=
  match p with
  | nil => v
  | k :: r =>
    match j with
    | JObj ms =>
      if existsb (fun m => String.eqb (fst m) k) ms
      then JObj (map (fun m => if String.eqb (fst m) k then (fst m, pg_set create r (snd m) v) else m) ms)
      else match r with nil => if create then normalize (JObj (ms ++ [(k, v)])) else j | _ => j end
    | JArr l =>
      match int_of_text k with
      | Some i =>
        let n := Z.of_nat (List.length l) in
        let i' := if Z.ltb i 0 then (n + i)%Z else i in
        if Z.leb 0 i' && Z.ltb i' n
        then JArr (firstn (Z.to_nat i') l ++ [pg_set create r (nth (Z.to_nat i') l JNull) v] ++ skipn (S (Z.to_nat i')) l)
        else match r with
             | nil => if create then (if Z.ltb i' 0 then JArr (v :: l) else JArr (l ++ [v])) else j
             | _ => j end
      | None => j
      end
    | _ => j
    end
  end.

(** [jsonb_insert (target, path, new [, after])]: in an array, before (or after) the element; in an object,
    a new member only *)
Definition pg_insert (after : bool) (p : list string) (j v : json) : json :=
  match rev p with
  | k :: rp =>
    let parent := rev rp in
    let fix go (q : list string) (t : json) : json :=
        match q with
        | nil => match t with
                 | JArr l => match int_of_text k with
                             | Some i => let n := Z.of_nat (List.length l) in
                                         let i' := if Z.ltb i 0 then (n + i)%Z else i in
                                         let pos := Z.to_nat (Z.max 0 (Z.min n (if after then i' + 1 else i')))%Z in
                                         JArr (firstn pos l ++ [v] ++ skipn pos l)
                             | None => t end
                 | JObj ms => if existsb (fun m => String.eqb (fst m) k) ms then t else normalize (JObj (ms ++ [(k, v)]))
                 | _ => t
                 end
        | x :: r => match t with
                    | JObj ms => JObj (map (fun m => if String.eqb (fst m) x then (fst m, go r (snd m)) else m) ms)
                    | JArr l => match int_of_text x with
                                | Some i => let n := Z.of_nat (List.length l) in
                                            let i' := if Z.ltb i 0 then (n + i)%Z else i in
                                            JArr (map (fun q => if Z.eqb (Z.of_nat (fst q)) i' then go r (snd q) else snd q) (combine (seq 0 (List.length l)) l))
                                | None => t end
                    | _ => t end
        end in
    go parent j
  | nil => j
  end.

(** [#-]: remove the path *)
Fixpoint pg_remove (p : list string) (j : json) : json :=
  match p with
  | nil => j
  | k :: r =>
    match j with
    | JObj ms => match r with
                 | nil => JObj (filter (fun m => negb (String.eqb (fst m) k)) ms)
                 | _ => JObj (map (fun m => if String.eqb (fst m) k then (fst m, pg_remove r (snd m)) else m) ms) end
    | JArr l => match int_of_text k with
                | Some i => let n := Z.of_nat (List.length l) in
                            let i' := if Z.ltb i 0 then (n + i)%Z else i in
                            match r with
                            | nil => JArr (map snd (filter (fun q => negb (Z.eqb (Z.of_nat (fst q)) i')) (combine (seq 0 (List.length l)) l)))
                            | _ => JArr (map (fun q => if Z.eqb (Z.of_nat (fst q)) i' then pg_remove r (snd q) else snd q) (combine (seq 0 (List.length l)) l)) end
                | None => j end
    | _ => j
    end
  end.

(** [jsonb || jsonb]: two objects are merged (the right one wins), arrays are concatenated, a scalar is
    wrapped in an array *)
Definition pg_concat (a b : json) : json :=
  match a, b with
  | JObj la, JObj lb => normalize (JObj (filter (fun m => negb (existsb (fun x => String.eqb (fst x) (fst m)) lb)) la ++ lb))
  | JArr la, JArr lb => JArr (la ++ lb)
  | JArr la, _ => JArr (la ++ [b])
  | _, JArr lb => JArr (a :: lb)
  | _, _ => JArr [a; b]
  end.

(** [jsonb - text] (a key, or the string elements of an array), [jsonb - integer] (an element) *)
Definition pg_minus_key (j : json) (k : string) : json :=
  match j with
  | JObj ms => JObj (filter (fun m => negb (String.eqb (fst m) k)) ms)
  | JArr l => JArr (filter (fun x => match x with JStr s => negb (String.eqb s k) | _ => true end) l)
  | _ => j
  end.

Definition pg_minus_idx (j : json) (i : Z) : json :=
  match j with
  | JArr l => let n := Z.of_nat (List.length l) in
              let i' := if Z.ltb i 0 then (n + i)%Z else i in
              JArr (map snd (filter (fun q => negb (Z.eqb (Z.of_nat (fst q)) i')) (combine (seq 0 (List.length l)) l)))
  | _ => j
  end.

(** [jsonb_strip_nulls]: the members whose value is [null], recursively; with [arr] (the second argument of
    PostgreSQL 18, [strip_in_arrays]) also the [null] elements of the arrays *)
Fixpoint strip_nulls_aux (arr : bool) (fuel : nat) (j : json) : json :=
  match fuel with
  | O => j
  | S f =>
    match j with
    | JObj ms => JObj (flat_map (fun m => match snd m with JNull => nil | v => [(fst m, strip_nulls_aux arr f v)] end) ms)
    | JArr l => JArr (map (strip_nulls_aux arr f)
                          (if arr then filter (fun v => match v with JNull => false | _ => true end) l else l))
    | _ => j
    end
  end.
Definition strip_nulls_arr (arr : bool) (j : json) : json := strip_nulls_aux arr (json_size j) j.
Definition strip_nulls (j : json) : json := strip_nulls_arr false j.
