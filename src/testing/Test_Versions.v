(** * Per-version flags (TODO 4.10): a construct introduced in version N is rejected before it *)
Require Import List String ZArith NArith.
Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.
Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax
        Dialects PostgreSQL MySQL SQLite MariaDB TiDB Versions.
Import ListNotations.
Open Scope string_scope.
Ltac check := vm_compute; reflexivity.
Notation c0 := (Attr_Z "c0").
Definition accepts (d : vsem) (q : squery) : bool := accepted_by (dialect_of d) (vs_supports d) (to_dialect d q).
Definition t := values_ [c0] [[int 1]; [int 2]].

(** [INTERSECT]: MySQL 8.0.31, MariaDB 10.3, TiDB 5.0 *)
Definition q_inter := set_op_ Inter Set_Distinct t t.
Example inter_80 : (accepts MySQL q_inter, accepts MySQL80 q_inter, accepts MySQL84 q_inter) = (true, false, true).
Proof. check. Qed.
Example inter_maria : (accepts MariaDB10_6 q_inter, accepts TiDB4 q_inter) = (true, false).
Proof. check. Qed.

(** window functions: MySQL 8.0.2, SQLite 3.25 *)
Definition q_win := window t [w_as w_row_number [] [] (Attr_Z "rn")].
Example win : (accepts MySQL57 q_win, accepts MySQL80 q_win, accepts SQLite3_24 q_win, accepts SQLite3_45 q_win)
              = (false, true, false, true).
Proof. check. Qed.

(** [RIGHT JOIN] in SQLite: 3.39 *)
Definition q_right := select_where [as_ (col c0) c0] [join J_Right (from_query t) (from_as t [(c0, Attr_Z "c1")]) c_true] c_true.
Example right_join : (accepts SQLite3_24 q_right, accepts SQLite3_45 q_right) = (false, true).
Proof. check. Qed.

(** a version only restricts: a query which the dialect rejects is rejected at every version *)
Example full_mysql : accepts MySQL84 (select_where [as_ (col c0) c0] [join J_Full (from_query t) (from_as t [(c0, Attr_Z "c1")]) c_true] c_true) = false.
Proof. check. Qed.
