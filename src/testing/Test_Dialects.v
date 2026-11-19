(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Differential tests: the same query run under PostgreSQL, MySQL, SQLite and    *)
(**   OceanBase (MySQL and Oracle modes). Every list below is, in this order, the   *)
(**   result in each of these dialects.                                             *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String ZArith NArith.

Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.

Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax
        Dialects PostgreSQL MySQL SQLite OceanBase.

Import Tuple.
Import ListNotations.
Open Scope string_scope.

Ltac check := vm_compute; reflexivity.

Notation x := (Attr_Z "x").
Notation nm := (Attr_string "nm").
Notation n := (Attr_Z "n").
Notation c := (Attr_Z "c").

Definition all : list vsem := 
  [PostgreSQL; MySQL; SQLite; OceanBaseMySQL; OceanBaseOracle].

(** * Running a query in a dialect *)

Definition db : db_state :=
  mk_insert 
    (create_table init_db (Rel "p") [nm; n])
    (Rel "p") [nm; n]
    [ [VS "Bob"; VZ 1]; [VS "bob"; VZ 2]; [VS "Alice"; VZ 3]; [NullS; VZ 4] ].

Definition run (d : vsem) (q : squery) : list (tuple (TD d)) :=
  eval_query_list ORN (dialect_of d) (_basesort _ db) (_instance _ db) (to_dialect d q).

Definition value_of (d : vsem) (t : tuple (TD d)) (a : attribute TNull) : NullValues.value := 
  dot (TD d) t a.

(** the first column [x] of the first row *)
Definition scalar (d : vsem) (q : squery) : NullValues.value :=
  match run d q with t :: _ => value_of d t x | nil => NullZ end.

Definition nrows (d : vsem) (q : squery) := List.length (run d q).

(** Equality of results: all the NULLs are equal, numbers are compared as numbers. *)
Definition veq (a b : NullValues.value) : bool :=
  match NullValues.is_null a, NullValues.is_null b with
  | true, true => true
  | false, false => match NullValues.sql_compare a b with Some Eq => true | _ => false end
  | _, _ => false
  end.

Definition sc (e : sexpr) : squery := select_where [as_ e x] [] c_true.

(** the value of the expression, in each dialect, is the given one *)
Definition values_are (mk : vsem -> sexpr) (expected : list NullValues.value) : bool :=
  forallb (fun p => veq (scalar (fst p) (sc (mk (fst p)))) (snd p)) (combine all expected).

Definition same (e : sexpr) := fun (_ : vsem) => e.

(** the condition is true, in each dialect *)
Definition holds_in (cond : scond) : list bool :=
  map (fun d => Nat.eqb (nrows d (select_where [as_ (int 1) x] [] cond)) 1) all.

(** * Arithmetic *)

(** [/] is the integer division in PostgreSQL and in SQLite, an exact division in MySQL
    and in Oracle. *)
Example div_ints : 
  values_are (same (fn "/" [int 7; int 2])) [VZ 3; VQ 7 2; VZ 3; VQ 7 2; VQ 7 2] = true.
Proof. check. Qed.

Example div_negative : 
  values_are (same (fn "/" [int (-7); int 2])) [VZ (-3); VQ (-7) 2; VZ (-3); VQ (-7) 2; VQ (-7) 2] = true.
Proof. check. Qed.

Example div_zero : 
  values_are (same (fn "/" [int 1; int 0])) [NullZ; NullZ; NullZ; NullZ; NullZ] = true.
Proof. check. Qed.

(** The remainder has the sign of the dividend; [mod(5, 0)] is NULL, but 5 in Oracle. *)
Example mod_negative : 
  values_are (same (fn "mod" [int (-5); int 3])) [VZ (-2); VZ (-2); VZ (-2); VZ (-2); VZ (-2)] = true.
Proof. check. Qed.

Example mod_zero : 
  values_are (same (fn "mod" [int 5; int 0])) [NullZ; NullZ; NullZ; NullZ; VZ 5] = true.
Proof. check. Qed.

(** Rounding is away from zero; in SQLite the result is a real. *)
Example round_half : 
  values_are (same (fn "round" [cst (VQ 5 2)])) [VZ 3; VZ 3; VZ 3; VZ 3; VZ 3] = true.
Proof. check. Qed.

Example round_negative_half : 
  values_are (same (fn "round" [cst (VQ (-5) 2)])) [VZ (-3); VZ (-3); VZ (-3); VZ (-3); VZ (-3)] = true.
Proof. check. Qed.

(** * Conditions as values: a boolean, or the integers 1 and 0 *)

Example condition_value : 
  values_are (same (e_cond (pred "<" [int 1; int 2]))) 
             [VB true; VZ 1; VZ 1; VZ 1; VZ 1] = true.
Proof. check. Qed.

(** * Comparison of values *)

(** Strings are compared without regard to case in MySQL (and OceanBase MySQL mode). *)
Example string_case : 
  holds_in (pred "=" [str "abc"; str "ABC"]) = [false; true; false; true; false].
Proof. check. Qed.

(** [LIKE] is case insensitive in MySQL, and in SQLite for ASCII. *)
Example like_case : 
  holds_in (pred "like" [str "ABC"; str "a%"]) = [false; true; true; true; false].
Proof. check. Qed.

(** A string and a number: not comparable in PostgreSQL (UNKNOWN here, an error in
    PostgreSQL); converted to a number in MySQL and Oracle; different in SQLite, where
    the numbers are smaller than the strings. *)
Example string_number_eq : 
  holds_in (pred "=" [str "1"; int 1]) = [false; true; false; true; true].
Proof. check. Qed.

Example string_number_not_eq : 
  holds_in (c_not (pred "=" [str "1"; int 1])) = [false; false; true; false; false].
Proof. check. Qed.

(** MySQL reads the prefix of a string which is used as a number. *)
Example string_prefix : 
  holds_in (pred "=" [str "12abc"; int 12]) = [false; true; false; true; false].
Proof. check. Qed.

(** The empty string is NULL in Oracle. *)
Example empty_is_null : 
  holds_in (pred "is null" [str ""]) = [false; false; false; false; true].
Proof. check. Qed.

Example empty_equals_empty : 
  holds_in (pred "=" [str ""; str ""]) = [true; true; true; true; false].
Proof. check. Qed.

(** * Strings *)

(** [NULL] in a concatenation: [||] is NULL in PostgreSQL, SQLite and MySQL (where it is
    the logical OR, here of a string read as 0 and of NULL), and ignores the NULL in Oracle. *)
Example concat_null_operator : 
  values_are (same (fn "||" [str "a"; cst NullS])) [NullZ; NullZ; NullZ; NullZ; VS "a"] = true.
Proof. check. Qed.

(** [concat] ignores the NULLs, except in MySQL. *)
Example concat_null_function : 
  values_are (same (fn "concat" [str "a"; cst NullS])) [VS "a"; NullZ; VS "a"; NullZ; VS "a"] = true.
Proof. check. Qed.

(** [||] is the logical OR in MySQL: ['1' || '0'] is 1. *)
Example pipes_or : 
  values_are (same (fn "||" [str "1"; str "0"])) [VS "10"; VZ 1; VS "10"; VZ 1; VS "10"] = true.
Proof. check. Qed.

(** [substr(s, 0, 3)] has four different results. *)
Example substr_zero : 
  values_are (same (fn "substr" [str "abcde"; int 0; int 3])) 
             [VS "ab"; VS ""; VS "ab"; VS ""; VS "abc"] = true.
Proof. check. Qed.

(** a negative start counts from the end, except in PostgreSQL *)
Example substr_negative : 
  values_are (same (fn "substr" [str "abcde"; int (-2)])) 
             [VS "abcde"; VS "de"; VS "de"; VS "de"; VS "de"] = true.
Proof. check. Qed.

Example length_empty : 
  values_are (same (fn "length" [str ""])) [VZ 0; VZ 0; VZ 0; VZ 0; NullZ] = true.
Proof. check. Qed.

(** * Functions over several arguments *)

(** [greatest] ignores the NULLs in PostgreSQL, and is NULL in MySQL and Oracle; the scalar
    [max] of SQLite is NULL. *)
Definition greatest_name (d : vsem) := if String.eqb (vs_name d) "SQLite" then "max" else "greatest".

Example greatest_null : 
  values_are (fun d => fn (greatest_name d) [int 1; cst NullZ; int 3]) 
             [VZ 3; NullZ; NullZ; NullZ; NullZ] = true.
Proof. check. Qed.

Example coalesce_empty : 
  values_are (same (fn "coalesce" [str ""; str "x"])) [VS ""; VS ""; VS ""; VS ""; VS "x"] = true.
Proof. check. Qed.

(** * Aggregates *)

Definition three := values_ [x] [ [int 1]; [int 2]; [cst NullZ] ].
Definition agg_of (f : string) := 
  select_where [as_ (agg f (col x)) x] [from_query three] c_true.

Definition agg_values (f : vsem -> string) (expected : list NullValues.value) : bool :=
  forallb (fun p => veq (scalar (fst p) (agg_of (f (fst p)))) (snd p)) (combine all expected).

Example count_ignores_nulls : 
  agg_values (fun _ => "count") [VZ 2; VZ 2; VZ 2; VZ 2; VZ 2] = true.
Proof. check. Qed.

Example sum_nulls : 
  agg_values (fun _ => "sum") [VZ 3; VZ 3; VZ 3; VZ 3; VZ 3] = true.
Proof. check. Qed.

Example avg_nulls : 
  agg_values (fun _ => "avg") [VQ 3 2; VQ 3 2; VQ 3 2; VQ 3 2; VQ 3 2] = true.
Proof. check. Qed.

(** the sum of nothing is NULL, but [total] of SQLite is 0 *)
Definition empty_agg (f : string) := 
  select_where [as_ (agg f (col x)) x] [from_query (select_where [as_ (col x) x] [from_query three] (c_not c_true))] c_true.

Example sum_empty : 
  forallb (fun d => veq (scalar d (empty_agg "sum")) NullZ) all = true.
Proof. check. Qed.

Example total_empty : 
  veq (scalar SQLite (empty_agg "total")) (VZ 0) = true.
Proof. check. Qed.

(** string aggregation has a different name, and a different default separator *)
Definition letters := values_ [x] [ [str "a"]; [cst NullS]; [str "b"] ].

Definition concat_agg_name (d : vsem) := 
  if String.eqb (vs_name d) "PostgreSQL" then "string_agg" 
  else if String.eqb (vs_name d) "OceanBase (Oracle mode)" then "listagg" 
  else "group_concat".

Example string_aggregation : 
  forallb (fun p => 
             veq (scalar (fst p) (select_where [as_ (agg (concat_agg_name (fst p)) (col x)) x] 
                                               [from_query letters] c_true)) (snd p))
          (combine all [VS "ab"; VS "a,b"; VS "a,b"; VS "a,b"; VS "ab"]) = true.
Proof. check. Qed.

(** * Grouping and ordering: collation, and the position of NULLs *)

Definition names := select_where [as_ (col nm) nm] [from_table "p"] c_true.

(** [SELECT DISTINCT nm FROM p]: ["Bob"] and ["bob"] are the same in MySQL. *)
Example distinct_count : 
  map (fun d => nrows d (select_distinct [as_ (col nm) nm] [from_table "p"] c_true)) all
  = [4; 3; 4; 3; 4]%nat.
Proof. check. Qed.

(** [SELECT count( * ) FROM p GROUP BY nm]: the number of groups *)
Example group_count : 
  map (fun d => nrows d (select_group [as_ count_star c] [from_table "p"] c_true [col nm] c_true)) all
  = [4; 3; 4; 3; 4]%nat.
Proof. check. Qed.

(** The first row of [SELECT nm FROM p ORDER BY nm] is NULL, except in PostgreSQL and Oracle. *)
Example null_first : 
  map (fun d => match run d (order_by names [o_by (col nm) Asc]) with
                | t :: _ => NullValues.is_null (value_of d t nm)
                | nil => false
                end) all
  = [false; true; true; true; false].
Proof. check. Qed.

(** In SQLite the numbers are smaller than the strings, whatever their type. *)
Definition mixed := values_ [x] [ [str "b"]; [int 2]; [int 1]; [str "a"] ].
Definition sorted d := 
  map (fun t => value_of d t x) (run d (order_by (select_where [as_ (col x) x] [from_query mixed] c_true) [o_by (col x) Asc])).

Example sqlite_order : 
  forallb (fun p => veq (fst p) (snd p)) (combine (sorted SQLite) [VZ 1; VZ 2; VS "a"; VS "b"]) = true.
Proof. check. Qed.

(** In MySQL, the strings are read as numbers to be compared with numbers: they are 0. *)
Example mysql_order : 
  forallb (fun p => veq (fst p) (snd p)) (combine (sorted MySQL) [VS "a"; VS "b"; VZ 1; VZ 2]) = true.
Proof. check. Qed.

(** * Which dialect accepts which query *)

Definition q_full_join := 
  select_star_where [join J_Full (from_table "p") (from_table "p") c_true] c_true.
Definition q_lateral := 
  select_star_where [join_lateral J_Inner (from_table "p") (from_table "p") c_true] c_true.
Definition q_intersect_all := set_op_ Inter Set_All names names.
Definition q_nulls_last := order_by names [o_by_nulls (col nm) Asc Nulls_Last].
Definition q_filter := 
  select_where [as_ (agg_filter "count" (col n) (pred ">" [col n; int 1])) c] [from_table "p"] c_true.
Definition q_condition_value := sc (e_cond (pred "<" [int 1; int 2])).

Definition acceptance (q : squery) := map (fun d => accepted_by (dialect_of d) (to_dialect d q)) all.

Example accepted_full_join : acceptance q_full_join = [true; false; true; true; true].
Proof. check. Qed.

(** [LATERAL] exists in OceanBase since 4.3.1 (grammar of the MySQL mode; documentation of both modes). *)
Example accepted_lateral : acceptance q_lateral = [true; true; false; true; true].
Proof. check. Qed.

Example accepted_intersect_all : acceptance q_intersect_all = [true; true; false; false; false].
Proof. check. Qed.

Example accepted_nulls_last : acceptance q_nulls_last = [true; false; true; false; true].
Proof. check. Qed.

Example accepted_filter : acceptance q_filter = [true; false; true; false; false].
Proof. check. Qed.

Example accepted_condition_value : acceptance q_condition_value = [true; true; true; true; false].
Proof. check. Qed.

(** * Which dialect has which function, predicate and aggregate *)

Definition q_string_agg := select_where [as_ (agg "string_agg" (col x)) x] [from_query letters] c_true.
Definition q_group_concat := select_where [as_ (agg "group_concat" (col x)) x] [from_query letters] c_true.
Definition q_listagg := select_where [as_ (agg "listagg" (col x)) x] [from_query letters] c_true.
Definition q_total := select_where [as_ (agg "total" (col x)) x] [from_query three] c_true.
Definition q_ifnull := sc (fn "ifnull" [int 1; int 2]).
Definition q_nvl := sc (fn "nvl" [int 1; int 2]).
Definition q_substr := sc (fn "substr" [str "abc"; int 1]).
Definition q_distinct_from := 
  select_where [as_ (int 1) x] [] (pred "is distinct from" [int 1; int 2]).
Definition q_null_safe := select_where [as_ (int 1) x] [] (pred "<=>" [int 1; int 2]).
Definition q_between := select_where [as_ (int 1) x] [] (pred "between" [int 1; int 0; int 2]).

(** PostgreSQL, MySQL, SQLite, OceanBase MySQL mode, OceanBase Oracle mode *)
Example has_string_agg : acceptance q_string_agg = [true; false; false; false; false].
Proof. check. Qed.
Example has_group_concat : acceptance q_group_concat = [false; true; true; true; false].
Proof. check. Qed.
Example has_listagg : acceptance q_listagg = [false; false; false; false; true].
Proof. check. Qed.
Example has_total : acceptance q_total = [false; false; true; false; false].
Proof. check. Qed.
Example has_ifnull : acceptance q_ifnull = [false; true; true; true; false].
Proof. check. Qed.
Example has_nvl : acceptance q_nvl = [false; false; false; false; true].
Proof. check. Qed.
Example has_substr : acceptance q_substr = [true; true; true; true; true].
Proof. check. Qed.
Example has_is_distinct_from : acceptance q_distinct_from = [true; false; true; false; false].
Proof. check. Qed.
Example has_null_safe_equal : acceptance q_null_safe = [false; true; false; true; false].
Proof. check. Qed.
Example has_between : acceptance q_between = [true; true; true; true; true].
Proof. check. Qed.
