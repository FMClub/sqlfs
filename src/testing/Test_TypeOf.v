(** * The static types of expressions (TODO 6.2)

    The expected types are those of PostgreSQL 16 ([SELECT pg_typeof (e) FROM t]) and MariaDB 10.11
    ([CREATE TABLE r AS SELECT e AS x FROM t], [SHOW COLUMNS]), on [t (a INT, s TEXT, d NUMERIC / DECIMAL)]:
    PostgreSQL integer and bigint, MariaDB int and bigint are [ST_Int]; numeric and decimal [ST_Decimal]; double
    precision and double [ST_Float]; text, mediumtext and varchar [ST_Text]. *)
Require Import List ZArith String.
Require Import FlatData SqlFull Values GenericInstance SqlSyntax SqlFullSyntax Typing TypeOf.
Import ListNotations.
Open Scope string_scope.

Definition sc : list cols := [[(Attr_Z "a", ST_Int); (Attr_string "s", ST_Text); (Attr_Q "d", ST_Decimal)]].
Definition ty fam e := typeof_e relname ORN fam nil sc e.
Definition a := col (Attr_Z "a").
Definition s := col (Attr_string "s").
Definition d := col (Attr_Q "d").
Definition dec15 := cst (VDi 15 1).

Ltac check := vm_compute; reflexivity.

(** expression, PostgreSQL, MariaDB *)
Example t_add : ty TF_PostgreSQL (fn "+" [a; int 1]) = Some ST_Int /\ ty TF_MySQL (fn "+" [a; int 1]) = Some ST_Int.
Proof. split; check. Qed.
Example t_add_dec : ty TF_PostgreSQL (fn "+" [a; d]) = Some ST_Decimal /\ ty TF_MySQL (fn "+" [a; d]) = Some ST_Decimal.
Proof. split; check. Qed.
Example t_mul_lit : ty TF_PostgreSQL (fn "*" [a; dec15]) = Some ST_Decimal /\ ty TF_MySQL (fn "*" [a; dec15]) = Some ST_Decimal.
Proof. split; check. Qed.
(** [a / 2]: integer in PostgreSQL, decimal(14,4) in MariaDB *)
Example t_div : ty TF_PostgreSQL (fn "/" [a; int 2]) = Some ST_Int /\ ty TF_MySQL (fn "/" [a; int 2]) = Some ST_Decimal.
Proof. split; check. Qed.
Example t_mod : ty TF_PostgreSQL (fn "%" [a; int 3]) = Some ST_Int /\ ty TF_MySQL (fn "%" [a; int 3]) = Some ST_Int.
Proof. split; check. Qed.
Example t_neg : ty TF_PostgreSQL (fn "neg" [a]) = Some ST_Int /\ ty TF_MySQL (fn "neg" [a]) = Some ST_Int.
Proof. split; check. Qed.
Example t_abs : ty TF_PostgreSQL (fn "abs" [d]) = Some ST_Decimal /\ ty TF_MySQL (fn "abs" [d]) = Some ST_Decimal.
Proof. split; check. Qed.
(** [round (a)], [floor (a)]: double precision in PostgreSQL, int in MariaDB; [ceil (d)]: numeric, int *)
Example t_round_int : ty TF_PostgreSQL (fn "round" [a]) = Some ST_Float /\ ty TF_MySQL (fn "round" [a]) = Some ST_Int.
Proof. split; check. Qed.
Example t_round_dec : ty TF_PostgreSQL (fn "round" [d]) = Some ST_Decimal /\ ty TF_MySQL (fn "round" [d]) = Some ST_Decimal.
Proof. split; check. Qed.
Example t_ceil_dec : ty TF_PostgreSQL (fn "ceil" [d]) = Some ST_Decimal /\ ty TF_MySQL (fn "ceil" [d]) = Some ST_Int.
Proof. split; check. Qed.
Example t_floor_int : ty TF_PostgreSQL (fn "floor" [a]) = Some ST_Float /\ ty TF_MySQL (fn "floor" [a]) = Some ST_Int.
Proof. split; check. Qed.
(** [a = 1]: boolean in PostgreSQL, int(1) in MariaDB *)
Example t_cmp : ty TF_PostgreSQL (e_cond (pred "=" [a; int 1])) = Some ST_Bool /\
                ty TF_MySQL (e_cond (pred "=" [a; int 1])) = Some ST_Int.
Proof. split; check. Qed.
Example t_upper : ty TF_PostgreSQL (fn "upper" [s]) = Some ST_Text /\ ty TF_MySQL (fn "upper" [s]) = Some ST_Text.
Proof. split; check. Qed.
Example t_concat : ty TF_PostgreSQL (fn "||" [s; str "x"]) = Some ST_Text /\ ty TF_MySQL (fn "concat" [s; str "x"]) = Some ST_Text.
Proof. split; check. Qed.
Example t_length : ty TF_PostgreSQL (fn "length" [s]) = Some ST_Int /\ ty TF_MySQL (fn "length" [s]) = Some ST_Int.
Proof. split; check. Qed.
Example t_substr : ty TF_PostgreSQL (fn "substr" [s; int 1; int 2]) = Some ST_Text /\
                   ty TF_MySQL (fn "substr" [s; int 1; int 2]) = Some ST_Text.
Proof. split; check. Qed.
Example t_coalesce : ty TF_PostgreSQL (fn "coalesce" [a; d]) = Some ST_Decimal /\ ty TF_MySQL (fn "coalesce" [a; d]) = Some ST_Decimal.
Proof. split; check. Qed.
Example t_nullif : ty TF_PostgreSQL (fn "nullif" [a; int 1]) = Some ST_Int /\ ty TF_MySQL (fn "nullif" [a; int 1]) = Some ST_Int.
Proof. split; check. Qed.
Example t_cast : ty TF_PostgreSQL (fn "cast_numeric" [a]) = Some ST_Decimal /\ ty TF_MySQL (fn "cast_numeric" [a]) = Some ST_Decimal.
Proof. split; check. Qed.
Example t_case : ty TF_PostgreSQL (e_case (pred ">" [a; int 1]) a d) = Some ST_Decimal /\
                 ty TF_MySQL (e_case (pred ">" [a; int 1]) a d) = Some ST_Decimal.
Proof. split; check. Qed.
(** [sum (a)]: bigint in PostgreSQL, decimal(32,0) in MariaDB; [avg (a)]: numeric, decimal *)
Example t_sum_int : ty TF_PostgreSQL (agg "sum" a) = Some ST_Int /\ ty TF_MySQL (agg "sum" a) = Some ST_Decimal.
Proof. split; check. Qed.
Example t_sum_dec : ty TF_PostgreSQL (agg "sum" d) = Some ST_Decimal /\ ty TF_MySQL (agg "sum" d) = Some ST_Decimal.
Proof. split; check. Qed.
Example t_avg : ty TF_PostgreSQL (agg "avg" a) = Some ST_Decimal /\ ty TF_MySQL (agg "avg" a) = Some ST_Decimal.
Proof. split; check. Qed.
Example t_count : ty TF_PostgreSQL count_star = Some ST_Int /\ ty TF_MySQL (agg "count" s) = Some ST_Int.
Proof. split; check. Qed.
Example t_min : ty TF_PostgreSQL (agg "min" s) = Some ST_Text /\ ty TF_MySQL (agg "max" d) = Some ST_Decimal.
Proof. split; check. Qed.
Example t_sqrt : ty TF_PostgreSQL (fn "sqrt" [a]) = Some ST_Float /\ ty TF_MySQL (fn "sqrt" [a]) = Some ST_Float.
Proof. split; check. Qed.
Example t_greatest : ty TF_PostgreSQL (fn "greatest" [a; d]) = Some ST_Decimal /\ ty TF_MySQL (fn "greatest" [a; d]) = Some ST_Decimal.
Proof. split; check. Qed.
(** a scalar subquery has the type of its column *)
Example t_sub : ty TF_PostgreSQL (e_sub (select_where [as_ (agg "max" a) (Attr_Z "m")] [from_table "t"] c_true)) = Some ST_Int.
Proof. check. Qed.
(** a type error: [CASE WHEN ... THEN 1 ELSE 'a'::text END] in PostgreSQL *)
Example t_case_error : ty TF_PostgreSQL (e_case (pred ">" [a; int 1]) a s) = None.
Proof. check. Qed.
(** SQLite: no static type *)
Example t_sqlite : ty TF_SQLite (fn "+" [a; int 1]) = Some ST_Unknown.
Proof. check. Qed.
