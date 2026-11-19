(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**                              The MariaDB dialect                                *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String ZArith NArith.

Require Import Bool3 OrderedSet SqlFull Values Dialects ValueKit MySQL.

Open Scope string_scope.

(** MariaDB is a fork of MySQL: the semantics of the values (three-valued comparisons, string to
    number conversions, [div_precision_increment], the aggregates, the functions of
    [MySQL.v]) is that of MySQL. The differences which concern queries, established by the
    source of the server ([sql/sql_yacc.yy], [sql/sys_vars.cc], [cmake/character_sets.cmake],
    trunk of November 2026):
    - the default collation is [utf8mb4_uca1400_ai_ci]: case and accent insensitive, and
      [PAD SPACE] (the variants without padding are named [..._nopad_...]);
    - the default [sql_mode] is [STRICT_TRANS_TABLES, ERROR_FOR_DIVISION_BY_ZERO,
      NO_ENGINE_SUBSTITUTION, NO_AUTO_CREATE_USER]: no [ONLY_FULL_GROUP_BY], so a column
      which is neither grouped nor aggregated is accepted (its value is the one of an
      arbitrary row, which is not modelled), and no [PIPES_AS_CONCAT], so [||] is the
      logical OR;
    - [INTERSECT [ALL]] and [EXCEPT [ALL]] ([union_option] is shared by the three set
      operators), [FETCH FIRST ... WITH TIES] ([only_or_with_ties]) and no [PERCENT];
    - [FILTER (WHERE ...)] on aggregates ([attach_func_filter] accepts [SUM_FUNC_ITEM]);
    - window frames in [ROWS] and [RANGE] mode only ([Window_frame::UNITS_ROWS],
      [UNITS_RANGE]: no [GROUPS]);
    - no [FULL JOIN] (the join productions have [LEFT], [RIGHT], [INNER], [CROSS],
      [NATURAL]) and no [LATERAL] (no such token in [sql/lex.h]);
    - [WITH ROLLUP] only: [WITH CUBE] is reserved and rejected ([ER_WRONG_USAGE]), and
      there is no [GROUPING SETS];
    - no [NULLS FIRST] / [NULLS LAST]: the token does not exist;
    - [WITH RECURSIVE] and [ANY] / [ALL] subqueries are supported. *)
Definition maria_supports (f : feature) : bool :=
  match f with
  | F_Full_Join | F_Lateral | F_Frame_Groups | F_Nulls_Order 
  | F_Grouping_Sets | F_Cube | F_Fetch_Percent => false
  | _ => true
  end.

(** The default session: [utf8mb4_uca1400_ai_ci] (PAD SPACE, case insensitive), no
    [ONLY_FULL_GROUP_BY] nor [PIPES_AS_CONCAT] in [sql_mode], [group_concat_max_len] = 1048576
    ([Sys_group_concat_max_len] in [sql/sys_vars.cc]). *)
Definition maria_default_session : my_session := mk_my_session true true 4 false false 1048576%N.

Definition MariaDB : vsem := mysql_vs maria_default_session "MariaDB" maria_supports.
