(** * System and information functions (TODO 2.9)

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

(** The values come from [default_env] ([SystemFuns.v]): a fresh session of [root] on database [test]. *)
Example sys_my_version : text MySQL (fn "version" []) = "8.0.36".
Proof. check. Qed.
Example sys_maria_version : text MariaDB (fn "version" []) = "11.4.2-MariaDB".
Proof. check. Qed.
Example sys_tidb_version : text TiDB (fn "version" []) = "8.0.11-TiDB-v8.1.0".
Proof. check. Qed.
Example sys_my_user : text MySQL (fn "current_user" []) = "root@localhost".
Proof. check. Qed.
Example sys_my_db : text MySQL (fn "database" []) = "test".
Proof. check. Qed.
Example sys_my_conn : text MySQL (fn "connection_id" []) = "1".
Proof. check. Qed.
(** [LAST_INSERT_ID (expr)] is [expr] *)
Example sys_my_lii : text MySQL (fn "last_insert_id" [int 42]) = "42".
Proof. check. Qed.
Example sys_my_row_count : text MySQL (fn "row_count" []) = "-1".
Proof. check. Qed.
Example sys_pg_user : text PostgreSQL (fn "current_user" []) = "root".
Proof. check. Qed.
Example sys_pg_db : text PostgreSQL (fn "current_database" []) = "test".
Proof. check. Qed.
Example sys_pg_schema : text PostgreSQL (fn "current_schema" []) = "public".
Proof. check. Qed.
Example sys_lite_version : text SQLite (fn "sqlite_version" []) = "3.45.1".
Proof. check. Qed.
Example sys_lite_changes : text SQLite (fn "changes" []) = "0".
Proof. check. Qed.
Example sys_ora_user : text OceanBaseOracle (fn "user" []) = "root".
Proof. check. Qed.
Example sys_ora_ctx : text OceanBaseOracle (fn "sys_context" [str "USERENV"; str "DB_NAME"]) = "test".
Proof. check. Qed.
Example sys_arity : fails MySQL (fn "version" [int 1]) = true.
Proof. check. Qed.
