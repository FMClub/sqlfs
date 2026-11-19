(** * Regular expressions (TODO 2.4)

    The functions of the C library ([sqrt], [exp], [ln], [sin], ...) are correctly rounded; the
    [numeric] versions of PostgreSQL have the scale of [numeric.c]. The expected texts are the ones of
    the engines. *)
Require Import List String ZArith NArith.

Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.

Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax
        Dialects ValueKit PostgreSQL MySQL SQLite OceanBase SpecRunner.

Import Tuple.
Import ListNotations.
Open Scope string_scope.

Ltac check := vm_compute; reflexivity.

Notation c0 := (Attr_Z "c0").

Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).

Definition text (d : vsem) (e : sexpr) : string :=
  match run d (select_where [as_ (fn "cast_string" [e]) c0] [] c_true) with
  | t :: nil => show_value (dot (TD d) t (out_attr 0))
  | _ => "?"
  end.

Definition fails (d : vsem) (e : sexpr) : bool :=
  match eval_query_result ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) 
                          (to_dialect d (select_where [as_ e c0] [] c_true)) with
  | QR_Error _ => true
  | _ => false
  end.

Definition dbl (n : Z) := cst (VFl false n 0).
Require Import MariaDB TiDB.
Definition s (x : string) := str x.
Definition holds (d : vsem) (c : scond) : bool :=
  match run d (select_where [as_ (int 1) c0] [] c) with nil => false | _ => true end.
Definition fails_c (d : vsem) (c : scond) : bool := fails d (e_cond c).

(** PostgreSQL ([regex.out], manual 9.7.3) *)
Example rx_1 : holds PostgreSQL (pred "~" [s "bbbbb"; s "^([bc])\1*$"]) = true.
Proof. check. Qed.

Example rx_2 : holds PostgreSQL (pred "~" [s "bbc"; s "^([bc])\1*$"]) = false.
Proof. check. Qed.

Example rx_3 : holds PostgreSQL (pred "~" [s "abc abc abc"; s "^(\w+)( \1)+$"]) = true.
Proof. check. Qed.

Example rx_4 : holds PostgreSQL (pred "~*" [s "ABC"; s "^abc$"]) = true.
Proof. check. Qed.

Example rx_5 : holds PostgreSQL (pred "!~" [s "abc"; s "^abc$"]) = false.
Proof. check. Qed.

Example rx_6 : fails_c PostgreSQL (pred "~" [s "a"; s "("]) = true.
Proof. check. Qed.

Example rx_7 : text PostgreSQL (fn "substring_regex" [s "asd TO foo"; s " TO (([a-z0-9._]+|""([^""]+|"""")+"")+)"]) = "foo".
Proof. check. Qed.

Example rx_8 : text PostgreSQL (fn "substring_regex" [s "foobar"; s "o.b"]) = "oob".
Proof. check. Qed.

Example rx_9 : text PostgreSQL (fn "substring_regex" [s "foobar"; s "o(.)b"]) = "o".
Proof. check. Qed.

Example rx_10 : text PostgreSQL (fn "regexp_replace" [s "foobarbaz"; s "b.."; s "X"]) = "fooXbaz".
Proof. check. Qed.

Example rx_11 : text PostgreSQL (fn "regexp_replace" [s "foobarbaz"; s "b.."; s "X"; s "g"]) = "fooXX".
Proof. check. Qed.

Example rx_12 : text PostgreSQL (fn "regexp_replace" [s "foobarbaz"; s "b(..)"; s "X\1Y"; s "g"]) = "fooXarYXazY".
Proof. check. Qed.

Example rx_13 : text PostgreSQL (fn "regexp_count" [s "ABCABCAXYaxy"; s "A."]) = "3".
Proof. check. Qed.

Example rx_14 : text PostgreSQL (fn "regexp_count" [s "ABCABCAXYaxy"; s "A."; int 1; s "i"]) = "4".
Proof. check. Qed.

Example rx_15 : text PostgreSQL (fn "regexp_instr" [s "number of your street, town zip, FR"; s "[^,]+"; int 1; int 2]) = "23".
Proof. check. Qed.

Example rx_16 : text PostgreSQL (fn "regexp_substr" [s "number of your street, town zip, FR"; s "[^,]+"; int 1; int 2]) = " town zip".
Proof. check. Qed.

(** the greediness of the whole expression: the first quantifier is lazy, so the shortest match is taken *)
Example rx_17 : text PostgreSQL (fn "regexp_substr" [s "abc01234xyz"; s "(.*?)(\d+)(.*)"]) = "abc0".
Proof. check. Qed.

Example rx_18 : text PostgreSQL (fn "regexp_substr" [s "abc01234xyz"; s "(.*)(\d+)(.*)"]) = "abc01234xyz".
Proof. check. Qed.

Example rx_19 : holds PostgreSQL (pred "similar to" [s "abc"; s "abc"]) = true.
Proof. check. Qed.

Example rx_20 : holds PostgreSQL (pred "similar to" [s "abc"; s "a"]) = false.
Proof. check. Qed.

Example rx_21 : holds PostgreSQL (pred "similar to" [s "abc"; s "%(b|d)%"]) = true.
Proof. check. Qed.

Example rx_22 : holds PostgreSQL (pred "similar to" [s "abc"; s "(b|c)%"]) = false.
Proof. check. Qed.


(** MySQL (manual 14.8.2) *)
Example rx_23 : text MySQL (fn "regexp_instr" [s "dog cat dog"; s "dog"]) = "1".
Proof. check. Qed.

Example rx_24 : text MySQL (fn "regexp_instr" [s "dog cat dog"; s "dog"; int 2]) = "9".
Proof. check. Qed.

Example rx_25 : text MySQL (fn "regexp_instr" [s "aa aaa aaaa"; s "a{4}"]) = "8".
Proof. check. Qed.

Example rx_26 : text MySQL (fn "regexp_like" [s "CamelCase"; s "CAMELCASE"]) = "1".
Proof. check. Qed.

Example rx_27 : text MySQL (fn "regexp_like" [s "CamelCase"; s "CAMELCASE"; s "c"]) = "0".
Proof. check. Qed.

Example rx_28 : text MySQL (fn "regexp_replace" [s "a b c"; s "b"; s "X"]) = "a X c".
Proof. check. Qed.

Example rx_29 : text MySQL (fn "regexp_replace" [s "abc def ghi"; s "[a-z]+"; s "X"; int 1; int 3]) = "abc def X".
Proof. check. Qed.

Example rx_30 : text MySQL (fn "regexp_replace" [s "abc"; s "(b)"; s "[$1]"]) = "a[b]c".
Proof. check. Qed.

Example rx_31 : text MySQL (fn "regexp_substr" [s "abc def ghi"; s "[a-z]+"]) = "abc".
Proof. check. Qed.

Example rx_32 : text MySQL (fn "regexp_substr" [s "abc def ghi"; s "[a-z]+"; int 1; int 3]) = "ghi".
Proof. check. Qed.

Example rx_33 : holds MySQL (pred "regexp" [s "Michael!"; s ".*"]) = true.
Proof. check. Qed.

Example rx_34 : holds MySQL (pred "regexp" [s "a"; s "^[a-d]"]) = true.
Proof. check. Qed.

Example rx_35 : fails MySQL (fn "regexp_like" [s "a"; s "a["]) = true.
Proof. check. Qed.


(** MariaDB (PCRE: [\n] in a replacement) *)
Example rx_36 : text MariaDB (fn "regexp_replace" [s "James Bond"; s "^(.*) (.*)$"; s "\2, \1"]) = "Bond, James".
Proof. check. Qed.

Example rx_37 : text MariaDB (fn "regexp_substr" [s "ab12cd"; s "[0-9]+"]) = "12".
Proof. check. Qed.

(** TiDB (RE2: no back reference) *)
Example rx_38 : fails TiDB (fn "regexp_like" [s "aa"; s "(a)\1"]) = true.
Proof. check. Qed.

Example rx_39 : text TiDB (fn "regexp_like" [s "aa"; s "(a)a"]) = "1".
Proof. check. Qed.


(** Oracle (SQL Language Reference) *)
Example rx_40 : text OceanBaseOracle (fn "regexp_count" [s "123123123123"; s "123"; int 3; s "i"]) = "3".
Proof. check. Qed.

Example rx_41 : text OceanBaseOracle (fn "regexp_substr" [s "500 Oracle Parkway, Redwood Shores, CA"; s ",[^,]+,"]) = ", Redwood Shores,".
Proof. check. Qed.

Example rx_42 : text OceanBaseOracle (fn "regexp_replace" [s "500   Oracle     Parkway"; s "( ){2,}"; s " "]) = "500 Oracle Parkway".
Proof. check. Qed.

Example rx_43 : text OceanBaseOracle (fn "regexp_instr" [s "500 Oracle Parkway, Redwood Shores, CA"; s "[^ ]+"; int 1; int 6]) = "37".
Proof. check. Qed.

Example rx_44 : holds OceanBaseOracle (pred "regexp_like" [s "Steven"; s "^Ste(v|ph)en$"]) = true.
Proof. check. Qed.


(** SQLite: [REGEXP] calls a user function which is not defined *)
Example rx_45 : fails_c SQLite (pred "regexp" [s "a"; s "a"]) = true.
Proof. check. Qed.


(** The queries [s ~ p] and [substring (s from p)] of PostgreSQL's [src/test/regress/expected/regex.out]
    which have a one-row result (generated); ['a' ~ '$()|^\1'] is left out: PostgreSQL answers [f] there,
    a consequence of its back-reference search loop ([cfindloop]), see [docs/functions/regex.md] *)
Definition pg_regex_cases : list bool := [
  Bool.eqb (holds PostgreSQL (pred "~" [s "bbbbb"; s "^([bc])\1*$"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "ccc"; s "^([bc])\1*$"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "xxx"; s "^([bc])\1*$"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "bbc"; s "^([bc])\1*$"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "b"; s "^([bc])\1*$"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "abc abc abc"; s "^(\w+)( \1)+$"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "abc abd abc"; s "^(\w+)( \1)+$"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "abc abc abd"; s "^(\w+)( \1)+$"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "abc abc abc"; s "^(.+)( \1)+$"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "abc abd abc"; s "^(.+)( \1)+$"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "abc abc abd"; s "^(.+)( \1)+$"])) false;
  String.eqb (text PostgreSQL (fn "substring_regex" [s "asd TO foo"; s " TO (([a-z0-9._]+|""([^""]+|"""")+"")+)"])) "foo";
  String.eqb (text PostgreSQL (fn "substring_regex" [s "a"; s "((a))+"])) "a";
  String.eqb (text PostgreSQL (fn "substring_regex" [s "a"; s "((a)+)"])) "a";
  Bool.eqb (holds PostgreSQL (pred "~" [s "xz"; s "x(?=[xy])"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "xy"; s "x(?=[xy])"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "xz"; s "x(?![xy])"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "xy"; s "x(?![xy])"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "xyy"; s "(?<=[xy])yy+"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "zyy"; s "(?<=[xy])yy+"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "xyy"; s "(?<![xy])yy+"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "zyy"; s "(?<![xy])yy+"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "a"; s "($|^)*"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "a"; s "(^)+^"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "a"; s "$($$)+"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "a"; s "($^)+"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "a"; s "(^$)*"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "aa bb cc"; s "(^(?!aa))+"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "aa x"; s "(^(?!aa)(?!bb)(?!cc))+"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "bb x"; s "(^(?!aa)(?!bb)(?!cc))+"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "cc x"; s "(^(?!aa)(?!bb)(?!cc))+"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "dd x"; s "(^(?!aa)(?!bb)(?!cc))+"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "a"; s "((((((a)*)*)*)*)*)*"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "a"; s "((((((a+|)+|)+|)+|)+|)+|)"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "x"; s "abcd(\m)+xyz"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "a"; s "^abcd*(((((^(a c(e?d)a+|)+|)+|)+|)+|a)+|)"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "x"; s "a^(^)bcd*xy(((((($a+|)+|)+|)+$|)+|)+|)^$"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "x"; s "xyz(\Y\Y)+"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "x"; s "x|(?:\M)+"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "Programmer"; s "(\w).*?\1"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "a"; s ".. ()|\1"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "a"; s "()*\1"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "a"; s "()+\1"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "xxx"; s "(.){0}(\1)"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "xxx"; s "((.)){0}(\2)"])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "xyz"; s "((.)){0}(\2){0}"])) true;
  Bool.eqb (holds PostgreSQL (pred "~" [s "abcdef"; s "^(.)\1|\1."])) false;
  Bool.eqb (holds PostgreSQL (pred "~" [s "abadef"; s "^((.)\2|..)\2"])) false
].

Example pg_regex_out : forallb (fun b => b) pg_regex_cases = true.
Proof. check. Qed.
