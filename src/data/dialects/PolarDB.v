(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**                       The PolarDB for MySQL dialect                             *)
(**                                                                                 *)
(************************************************************************************)

Require Import String.

Require Import SqlFull Dialects MySQL.

Open Scope string_scope.

(** PolarDB for MySQL (the MySQL-compatible edition of Alibaba Cloud, not PolarDB-X nor the
    PostgreSQL or Oracle editions) follows community MySQL by minor version: the engine 8.0.2
    is compatible with MySQL 8.0.18 and earlier (documentation: syntax compatibility
    description, engine versions). The queries therefore have the semantics of MySQL 8.0, and
    the constructs which MySQL added after 8.0.18 are missing: [INTERSECT] and [EXCEPT]
    (MySQL 8.0.31). The default collation is [utf8mb4_0900_ai_ci]. *)
Definition polar_supports (f : feature) : bool :=
  match f with
  | F_Intersect | F_Intersect_All | F_Except | F_Except_All => false
  | _ => my_supports f
  end.

Definition PolarDB : vsem := mysql_vs my_default_session "PolarDB for MySQL" polar_supports.
