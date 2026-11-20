(** * Static types of the branches of UNION, CASE, COALESCE (TODO 1.9, 6.2)

    The values of the model carry their dynamic type ([Value_I], [Value_D], [Value_F], [Value_T], ...); the
    static type of a column of a set operation, or of the result of [CASE] and [COALESCE], is the common type of
    the static types of its branches, which each family computes in its own way:
    - PostgreSQL ([select_common_type], [parse_coerce.c]): the branches must be of the same category (numeric,
      string, boolean, date and time, JSON); in a category the preferred type wins (integer < numeric < double
      precision, date < timestamp); an untyped literal ([unknown]) and NULL take the type of the others; two
      categories are an error ("UNION types integer and text cannot be matched");
    - the MySQL family ([Item_type_holder::join_types], [Field::field_type_merge]): numbers merge (integer and
      decimal give decimal, a float gives double); a number and a string, or a date and a string, give a
      string; a date and a timestamp give a timestamp; there is no error;
    - SQLite: no static type (a column of a compound query has no declared type): no error;
    - Oracle mode ([ORA-01790: expression must have same datatype as corresponding expression]): the branches
      must be of the same group (numbers, character strings, dates and timestamps), NULL takes the type of the
      others.
    [common_type_of fam l] folds the common type over the branches; [None] is the error of the engine.
    Checked on live engines (PostgreSQL 16.15, MariaDB 10.11): the cases of [Test_Typing.v] give the types which
    [pg_typeof] and the columns of [CREATE TABLE ... AS SELECT ... UNION ...] show, and the errors. *)
Require Import List ZArith Bool String.
Open Scope bool_scope.
Require Import Values Dialects.
Import ListNotations.
Import NullValues.

Inductive stype : Type :=
  | ST_Null | ST_Unknown | ST_Bool | ST_Int | ST_Decimal | ST_Float | ST_Text | ST_Date | ST_Time
  | ST_Timestamp | ST_Json | ST_Interval.

Definition stype_eqb (a b : stype) : bool :=
  match a, b with
  | ST_Null, ST_Null | ST_Unknown, ST_Unknown | ST_Bool, ST_Bool | ST_Int, ST_Int | ST_Decimal, ST_Decimal
  | ST_Float, ST_Float | ST_Text, ST_Text | ST_Date, ST_Date | ST_Time, ST_Time | ST_Timestamp, ST_Timestamp
  | ST_Json, ST_Json | ST_Interval, ST_Interval => true
  | _, _ => false
  end.

(** the static type of a constant: a NULL has none (the model does not keep the type of a typed NULL);
    [unknown] marks the string literals of PostgreSQL, whose type comes from the context *)
Definition stype_of_value (literal_unknown : bool) (v : value) : stype :=
  match v with
  | Value_string (Some _) => if literal_unknown then ST_Unknown else ST_Text
  | Value_C (Some _) => ST_Text
  | Value_Z (Some _) | Value_I (Some _) => ST_Int
  | Value_bool (Some _) => ST_Bool
  | Value_Q (Some _) | Value_D (Some _) => ST_Decimal
  | Value_F (Some _) => ST_Float
  | Value_T (Some (_, k)) =>
    match Nat.modulo k 10 with 0 => ST_Date | 1 => ST_Time | _ => ST_Timestamp end
  | Value_V (Some _) => ST_Interval
  | Value_J (Some _) => ST_Json
  | _ => ST_Null
  end.

Inductive type_family : Type := TF_PostgreSQL | TF_MySQL | TF_SQLite | TF_Oracle.

Definition pg_category (t : stype) : nat :=
  match t with
  | ST_Int | ST_Decimal | ST_Float => 1
  | ST_Text => 2
  | ST_Bool => 3
  | ST_Date | ST_Time | ST_Timestamp => 4
  | ST_Json => 5
  | ST_Interval => 6
  | ST_Null | ST_Unknown => 0
  end.

(** the preferred type of a numeric or temporal category: the larger rank wins *)
Definition rank (t : stype) : nat :=
  match t with
  | ST_Int => 1 | ST_Decimal => 2 | ST_Float => 3 | ST_Date => 1 | ST_Timestamp => 2 | _ => 0
  end.

Definition wider (a b : stype) : stype := if Nat.leb (rank a) (rank b) then b else a.

Definition common_type (fam : type_family) (a b : stype) : option stype :=
  match a, b with
  | ST_Null, t | t, ST_Null => Some t
  | _, _ =>
    match fam with
    | TF_PostgreSQL =>
      match a, b with
      | ST_Unknown, ST_Unknown => Some ST_Text
      | ST_Unknown, t | t, ST_Unknown => Some t
      | _, _ =>
        if Nat.eqb (pg_category a) (pg_category b)
        then if Nat.eqb (pg_category a) 4 && negb (stype_eqb a b) && (stype_eqb a ST_Time || stype_eqb b ST_Time)
             then None (* time does not mix with date or timestamp *)
             else Some (wider a b)
        else None
      end
    | TF_MySQL =>
      match a, b with
      | (ST_Int | ST_Decimal | ST_Float | ST_Bool), (ST_Int | ST_Decimal | ST_Float | ST_Bool) =>
        Some (if stype_eqb a ST_Bool then wider ST_Int b else if stype_eqb b ST_Bool then wider a ST_Int else wider a b)
      | (ST_Date | ST_Timestamp), (ST_Date | ST_Timestamp) => Some (wider a b)
      | _, _ => if stype_eqb a b then Some a else Some ST_Text
      end
    | TF_SQLite => Some (if stype_eqb a b then a else ST_Unknown)
    | TF_Oracle =>
      match a, b with
      | (ST_Int | ST_Decimal | ST_Float), (ST_Int | ST_Decimal | ST_Float) => Some (wider a b)
      | (ST_Date | ST_Timestamp), (ST_Date | ST_Timestamp) => Some (wider a b)
      | _, _ => if stype_eqb a b then Some a else None
      end
    end
  end.

Definition common_type_of (fam : type_family) (l : list stype) : option stype :=
  fold_left (fun acc t => match acc with Some a => common_type fam a t | None => None end) l (Some ST_Null).

(** the family of a dialect *)
Definition family_of (d : vsem) : type_family :=
  if String.eqb (vs_name d) "PostgreSQL" then TF_PostgreSQL
  else if String.eqb (vs_name d) "SQLite" then TF_SQLite
  else if String.eqb (vs_name d) "OceanBase (Oracle mode)" then TF_Oracle
  else TF_MySQL.

(** the type of the column of a set operation, or of [CASE] / [COALESCE], whose branches are the constants [l] *)
Definition branches_type (d : vsem) (l : list value) : option stype :=
  let fam := family_of d in
  common_type_of fam (map (stype_of_value (match fam with TF_PostgreSQL => true | _ => false end)) l).

(** NULL is neutral, and the error is absorbing *)
Lemma common_type_null_l : forall fam t, common_type fam ST_Null t = Some t.
Proof. intros fam t; destruct t; reflexivity. Qed.

Lemma common_type_of_error :
  forall fam l, fold_left (fun acc t => match acc with Some a => common_type fam a t | None => None end) l None = None.
Proof. intros fam l; induction l as [ | x l IH]; [reflexivity | exact IH]. Qed.
