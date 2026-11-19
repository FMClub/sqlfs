(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**                    The Percona Server for MySQL dialect                         *)
(**                                                                                 *)
(************************************************************************************)

Require Import String.

Require Import SqlFull Dialects MySQL.

Open Scope string_scope.

(** Percona Server for MySQL is MySQL with additional features (performance and
    instrumentation, the hash and digest functions, per-column compression, enforced
    encryption: see the feature comparison of its documentation). It keeps the SQL syntax and
    the semantics of the queries of the MySQL release it is built on: its dialect is that of
    MySQL 8.4 (default collation [utf8mb4_0900_ai_ci], [ONLY_FULL_GROUP_BY] in the default
    [sql_mode], [INTERSECT] and [EXCEPT] with [ALL], [LATERAL], [WITH ROLLUP] only).
    The extra functions do not change the evaluation of the queries of [SqlFull]; they are
    not in the tables. *)
Definition Percona : vsem := mysql_vs my_default_session "Percona Server for MySQL" my_supports.
