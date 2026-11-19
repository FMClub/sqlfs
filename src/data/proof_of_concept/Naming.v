(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   The names of the output columns (TODO 3.9).                                   *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String Ascii.
Require Import SqlFull Values GenericInstance SqlFullSyntax.

Import ListNotations.
Open Scope string_scope.

(** The name of the column of a [SELECT] item without alias.

    PostgreSQL ([FigureColname], [src/backend/parser/parse_target.c]): a column reference gives its name,
    a function or an aggregate its name, a [CASE] ["case"], a cast the name of the type; anything else is
    ["?column?"]. MySQL and SQLite name such a column by the text of the expression as written: the
    translator keeps it. Duplicate names are allowed in a result, and are an error when a derived table
    which has them is referred to by name ([column reference is ambiguous]). *)
Definition last_part (s : string) : string :=
  match index 0 "." s with
  | Some i => let r := substring (S i) (String.length s - S i) s in
              match index 0 "." r with Some _ => r | None => r end
  | None => s
  end.

Definition attr_name (a : attribute) : string :=
  match a with Attr_string n | Attr_Z n | Attr_bool n | Attr_Q n => last_part n end.

(** the type names of the casts *)
Definition cast_type_name (f : string) : option string :=
  match f with
  | "cast_int" => Some "int4" | "cast_smallint" => Some "int2" | "cast_bigint" => Some "int8"
  | "cast_numeric" | "cast_decimal" => Some "numeric" | "cast_float8" => Some "float8" | "cast_float4" => Some "float4"
  | "cast_string" => Some "text" | "cast_bool" => Some "bool" | "cast_date" => Some "date"
  | "cast_time" => Some "time" | "cast_timestamp" => Some "timestamp" | "cast_timestamptz" => Some "timestamptz"
  | "cast_interval" => Some "interval" | "cast_json" => Some "json" | "cast_jsonb" => Some "jsonb"
  | _ => None
  end.

(** an internal name of an operator is not the name of a function *)
Definition operator_names : list string :=
  ["+"; "-"; "*"; "/"; "%"; "plus"; "minus"; "mult"; "div"; "mod"; "opp"; "neg"; "||"; "and"; "or"; "not";
   "&"; "|"; "#"; "~"; "<<"; ">>"; "->"; "->>"; "#>"; "#>>"; "#-"; "subscript"; "slice"; "trim_both";
   "trim_leading"; "trim_trailing"; "substring_regex"].

Definition pg_colname (e : sexpr) : string :=
  match e with
  | SqlFull.E_Col _ _ a => attr_name a
  | SqlFull.E_Fun (Values.Symbol _ f) _ =>
    match cast_type_name f with
    | Some t => t
    | None => if existsb (String.eqb f) operator_names then "?column?"
              else match f with
                   | "trim_both" | "trim_leading" | "trim_trailing" => "btrim"
                   | "array" => "array"
                   | _ => f
                   end
    end
  | SqlFull.E_Agg (Values.Aggregate a) _ _ _ | SqlFull.E_AggX (Values.Aggregate a) _ _ _ _ _ =>
    if String.eqb a "count(*)" then "count" else a
  | SqlFull.E_Case _ _ _ => "case"
  | _ => "?column?"
  end.
