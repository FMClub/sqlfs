(** * The static types of the branches of UNION, CASE, COALESCE (TODO 1.9, 6.2) *)
Require Import List ZArith String.
Require Import Values Dialects Typing PostgreSQL MySQL SQLite OceanBase.
Import ListNotations NullValues.
Open Scope string_scope.

(** PostgreSQL: [SELECT 1 UNION SELECT 'a']: the literal is [unknown] and takes the type integer (the engine then
    fails on its conversion); [SELECT 1 UNION SELECT 'a'::text]: "UNION types integer and text cannot be matched" *)
Example pg_unknown : branches_type PostgreSQL.PostgreSQL [Value_Z (Some 1%Z); Value_string (Some "a")] = Some ST_Int.
Proof. reflexivity. Qed.
Example pg_text_int : common_type_of TF_PostgreSQL [ST_Int; ST_Text] = None.
Proof. reflexivity. Qed.
(** the preferred type of a category: [1 UNION 1.5] is numeric, with a double precision it is double precision *)
Example pg_numeric : common_type_of TF_PostgreSQL [ST_Int; ST_Decimal] = Some ST_Decimal.
Proof. reflexivity. Qed.
Example pg_float : common_type_of TF_PostgreSQL [ST_Int; ST_Decimal; ST_Float] = Some ST_Float.
Proof. reflexivity. Qed.
Example pg_date_ts : common_type_of TF_PostgreSQL [ST_Date; ST_Timestamp] = Some ST_Timestamp.
Proof. reflexivity. Qed.
(** [true UNION 1]: "UNION types boolean and integer cannot be matched" *)
Example pg_bool_int : common_type_of TF_PostgreSQL [ST_Bool; ST_Int] = None.
Proof. reflexivity. Qed.
(** NULL takes the type of the other branches *)
Example pg_null : common_type_of TF_PostgreSQL [ST_Null; ST_Int; ST_Null] = Some ST_Int.
Proof. reflexivity. Qed.

(** MySQL: [1 UNION 'a'] is a string column; [1 UNION 1.5] decimal; a date and a string give a string; a
    boolean is an integer *)
Example my_int_text : branches_type MySQL.MySQL [Value_Z (Some 1%Z); Value_string (Some "a")] = Some ST_Text.
Proof. reflexivity. Qed.
Example my_numeric : common_type_of TF_MySQL [ST_Int; ST_Decimal] = Some ST_Decimal.
Proof. reflexivity. Qed.
Example my_date_text : common_type_of TF_MySQL [ST_Date; ST_Text] = Some ST_Text.
Proof. reflexivity. Qed.
Example my_bool_int : common_type_of TF_MySQL [ST_Bool; ST_Int] = Some ST_Int.
Proof. reflexivity. Qed.

(** Oracle mode: [SELECT 1 FROM DUAL UNION SELECT 'a' FROM DUAL]: ORA-01790 *)
Example ora_int_text : branches_type OceanBaseOracle [Value_Z (Some 1%Z); Value_string (Some "a")] = None.
Proof. reflexivity. Qed.
Example ora_numbers : common_type_of TF_Oracle [ST_Int; ST_Decimal] = Some ST_Decimal.
Proof. reflexivity. Qed.

(** SQLite: no static type, no error *)
Example sqlite_any : branches_type SQLite.SQLite [Value_Z (Some 1%Z); Value_string (Some "a")] <> None.
Proof. discriminate. Qed.
