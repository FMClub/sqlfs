(** * Functions added by the dialect closeouts (TODO 4.1-4.8) *)
Require Import List String ZArith NArith.
Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.
Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax
        Dialects PostgreSQL MySQL SQLite OceanBase MariaDB TiDB SpecRunner.
Import Tuple.
Import ListNotations.
Open Scope string_scope.
Ltac check := vm_compute; reflexivity.
Notation c0 := (Attr_Z "c0").
Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).
Definition val (d : vsem) (e : sexpr) : string :=
  match run d (select_where [as_ e c0] [] c_true) with
  | t :: nil => show_value (dot (TD d) t c0)
  | _ => "?"
  end.

(** ** PostgreSQL (4.1) *)
Example pg_scale : val PostgreSQL (fn "scale" [cst (VD 12340 3)]) = "3".
Proof. check. Qed.
Example pg_min_scale : val PostgreSQL (fn "min_scale" [cst (VD 12340 3)]) = "2".
Proof. check. Qed.
Example pg_trim_scale : val PostgreSQL (fn "trim_scale" [cst (VD 12340 3)]) = "12.34".
Proof. check. Qed.
Example pg_to_bin : val PostgreSQL (fn "to_bin" [int 10]) = "1010".
Proof. check. Qed.
Example pg_to_oct : val PostgreSQL (fn "to_oct" [int (-1)]) = "37777777777".
Proof. check. Qed.
Example pg_char_alias : val PostgreSQL (fn "character_length" [str "abc"]) = "3".
Proof. check. Qed.
