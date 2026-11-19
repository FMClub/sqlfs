(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**                              The TiDB dialect                                   *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String ZArith NArith.

Require Import Bool3 OrderedSet SqlFull Values Dialects ValueKit MySQL.

Open Scope string_scope.

(** TiDB speaks the MySQL dialect: the semantics of the values is that of [MySQL.v]. What
    differs, established by the source of TiDB ([pkg/parser/parser.y],
    [pkg/parser/mysql/const.go], [pkg/parser/charset/charset.go],
    [pkg/planner/core/logical_plan_builder.go], master of November 2026):
    - the default collation is [utf8mb4_bin] with the attribute [PadSpace]
      ([charset.go]): strings are compared byte by byte, so the comparison is case
      sensitive, but trailing spaces are not significant;
    - the default [sql_mode] has [ONLY_FULL_GROUP_BY] ([mysql.DefaultSQLMode]), as MySQL;
    - [INTERSECT ALL] and [EXCEPT ALL] ([ast.IntersectAll], [ast.ExceptAll]);
    - [LATERAL] derived tables ([TableFactor: "LATERAL" SubSelect ...]) and
      [FULL OUTER JOIN] (the token [fullJoinType]);
    - [WITH ROLLUP] and the function [GROUPING], but no [CUBE] and no [GROUPING SETS];
    - window frames [ROWS] and [RANGE]: [GROUPS] is parsed and rejected by the planner
      ([ErrNotSupportedYet("GROUPS")]);
    - no [FILTER] clause, no [NULLS FIRST] / [NULLS LAST] in [ORDER BY], and
      [FETCH FIRST n ROWS ONLY] without [WITH TIES] nor [PERCENT];
    - [WITH RECURSIVE] and [ANY] / [ALL] subqueries are supported. *)
Definition tidb_supports (f : feature) : bool :=
  match f with
  | F_Frame_Groups | F_Filter_Agg | F_Nulls_Order | F_Grouping_Sets | F_Cube
  | F_Fetch_Ties | F_Fetch_Percent | F_Bare_Column => false
  | _ => true
  end.

Definition TiDB : vsem := mysql_vs true false "TiDB" tidb_supports.
