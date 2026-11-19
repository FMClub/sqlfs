(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   Tests of the collations (TODO 1.3).                                           *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String ZArith NArith.

Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.

Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax
        Dialects ValueKit PostgreSQL MySQL SQLite OceanBase TiDB MariaDB SpecRunner.

Import Tuple.
Import ListNotations.
Open Scope string_scope.

Ltac check := vm_compute; reflexivity.

Notation c0 := (Attr_string "c0").

Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).

Definition fails (d : vsem) (c : scond) : bool :=
  match eval_query_result ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) 
                          (to_dialect d (select_where [as_ (int 1) (Attr_Z "c1")] [] c)) with
  | QR_Error _ => true
  | _ => false
  end.

Definition holds (d : vsem) (c : scond) : bool :=
  Nat.eqb (List.length (run d (select_where [as_ (int 1) (Attr_Z "c1")] [] c))) 1.

Definition words := values_ [c0] [[str "_"]; [str "a"]; [str "B"]].

Definition sorted (d : vsem) : list string :=
  map (fun t => show_value (dot (TD d) t c0))
      (run d (order_by (select_where [as_ (col c0) c0] [from_as words [(c0, c0)]] c_true) [o_by (col c0) Asc])).

(** The order of ['_'], ['a'], ['B']:
    - [utf8mb4_general_ci] (OceanBase) weighs a letter by its upper case: [a < B < _];
    - [utf8mb4_0900_ai_ci] (MySQL 8): the punctuation comes before the letters: [_ < a < B];
    - [utf8mb4_bin] (TiDB) and [C] (PostgreSQL): the bytes: [B < _ < a]. *)
Example order_general_ci : sorted OceanBaseMySQL = ["a"; "B"; "_"].
Proof. check. Qed.

Example order_uca900 : sorted MySQL = ["_"; "a"; "B"].
Proof. check. Qed.

Example order_binary : map sorted [TiDB; PostgreSQL] = [["B"; "_"; "a"]; ["B"; "_"; "a"]].
Proof. check. Qed.

(** accents: equal under the [_ai_ci] collations and [general_ci], different under [bin] and [C] *)
Example accent : 
  map (fun d => holds d (pred "=" [str "á"; str "a"])) [MySQL; OceanBaseMySQL; MariaDB; TiDB; PostgreSQL] 
  = [true; true; true; false; false].
Proof. check. Qed.

(** expansions: [ß] is [ss] in UCA 9.0.0, and [s] in [general_ci] *)
Example eszett :
  map (fun d => holds d (pred "=" [str "ß"; str "ss"])) [MySQL; OceanBaseMySQL] = [true; false].
Proof. check. Qed.

Example eszett_general :
  holds OceanBaseMySQL (pred "=" [str "ß"; str "s"]) = true.
Proof. check. Qed.

(** [COLLATE] *)
Example collate_bin : holds MySQL (pred "=" [fn "collate" [str "a"; str "utf8mb4_bin"]; str "A"]) = false.
Proof. check. Qed.

Example collate_nocase : holds SQLite (pred "=" [fn "collate" [str "a"; str "NOCASE"]; str "A"]) = true.
Proof. check. Qed.

Example sqlite_binary : holds SQLite (pred "=" [str "a"; str "A"]) = false.
Proof. check. Qed.

Example collate_rtrim : holds SQLite (pred "=" [fn "collate" [str "a  "; str "RTRIM"]; str "a"]) = true.
Proof. check. Qed.

(** two different explicit collations: [Illegal mix of collations] *)
Example illegal_mix : 
  fails MySQL (pred "=" [fn "collate" [str "a"; str "utf8mb4_bin"]; fn "collate" [str "a"; str "utf8mb4_general_ci"]]) = true.
Proof. check. Qed.

Example unknown_collation : 
  fails MySQL (pred "=" [fn "collate" [str "a"; str "no_such_collation"]; str "a"]) = true.
Proof. check. Qed.

(** [LIKE] compares the characters by the collation; [_] is one character, not one byte *)
Example like_accent : 
  map (fun d => holds d (pred "like" [str "Á"; str "a"])) [MySQL; TiDB] = [true; false].
Proof. check. Qed.

Example like_one_char : holds MySQL (pred "like" [str "á"; str "_"]) = true.
Proof. check. Qed.

(** [LOCATE] counts characters *)
Definition loc (d : vsem) (e : sexpr) : string :=
  match run d (select_where [as_ e (Attr_Z "c1")] [] c_true) with
  | t :: nil => show_value (dot (TD d) t (Attr_Z "c1"))
  | _ => "?"
  end.

Example locate_chars : loc MySQL (fn "locate" [str "b"; str "ábc"]) = "2".
Proof. check. Qed.
