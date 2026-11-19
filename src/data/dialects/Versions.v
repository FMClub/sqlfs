(** * Per-version flags of the dialects (TODO 4.10)

    A version is a list of numbers ([8; 0; 31] is MySQL 8.0.31), compared lexicographically. For each family,
    [introduced] gives the first release which accepts a construct, from the release notes of the engine; a
    construct which is not in the table is accepted by every version which the dialect record covers.
    [at_version d fam v] is the dialect [d] restricted to the constructs of version [v]. *)
Require Import List String Bool Arith.
Require Import SqlFull Dialects PostgreSQL MySQL SQLite MariaDB TiDB.
Import ListNotations.
Open Scope string_scope.

Definition version := list nat.

Fixpoint version_le (a b : version) : bool :=
  match a, b with
  | nil, _ => true
  | _ :: _, nil => forallb (Nat.eqb 0) a
  | x :: a', y :: b' => if Nat.ltb x y then true else if Nat.ltb y x then false else version_le a' b'
  end.

Inductive family : Type := Fam_PostgreSQL | Fam_MySQL | Fam_SQLite | Fam_MariaDB | Fam_TiDB.

(** The first release which accepts a construct. Sources: the release notes of PostgreSQL (8.4, 9.3, 9.4, 9.5,
    11, 13), the MySQL 8.0 release notes (8.0.1, 8.0.2, 8.0.14, 8.0.31), the SQLite release history (3.8.3,
    3.15.0, 3.25.0, 3.28.0, 3.30.0, 3.39.0), the MariaDB release notes (10.2.1, 10.2.2, 10.3.0, 10.5.0, 10.6.0),
    and the TiDB release notes (3.0, 5.0, 5.1). *)
Definition introduced (fam : family) (f : feature) : option version :=
  match fam, f with
  | Fam_PostgreSQL, (F_Window | F_With | F_Recursive) => Some [8; 4]
  | Fam_PostgreSQL, F_Lateral => Some [9; 3]
  | Fam_PostgreSQL, F_Filter_Agg => Some [9; 4]
  | Fam_PostgreSQL, (F_Grouping_Sets | F_Rollup | F_Cube) => Some [9; 5]
  | Fam_PostgreSQL, (F_Frame_Groups | F_Frame_Exclusion) => Some [11]
  | Fam_PostgreSQL, F_Fetch_Ties => Some [13]
  | Fam_MySQL, (F_With | F_Recursive) => Some [8; 0; 1]
  | Fam_MySQL, F_Window => Some [8; 0; 2]
  | Fam_MySQL, F_Lateral => Some [8; 0; 14]
  | Fam_MySQL, (F_Intersect | F_Except | F_Intersect_All | F_Except_All) => Some [8; 0; 31]
  | Fam_SQLite, (F_With | F_Recursive) => Some [3; 8; 3]
  | Fam_SQLite, F_Row_In => Some [3; 15]
  | Fam_SQLite, F_Window => Some [3; 25]
  | Fam_SQLite, (F_Frame_Groups | F_Frame_Exclusion) => Some [3; 28]
  | Fam_SQLite, (F_Filter_Agg | F_Nulls_Order) => Some [3; 30]
  | Fam_SQLite, (F_Right_Join | F_Full_Join) => Some [3; 39]
  | Fam_MariaDB, (F_Window | F_With) => Some [10; 2; 1]
  | Fam_MariaDB, F_Recursive => Some [10; 2; 2]
  | Fam_MariaDB, (F_Intersect | F_Except) => Some [10; 3]
  | Fam_MariaDB, (F_Intersect_All | F_Except_All) => Some [10; 5]
  | Fam_MariaDB, F_Fetch_Ties => Some [10; 6]
  | Fam_TiDB, F_Window => Some [3]
  | Fam_TiDB, (F_Intersect | F_Except) => Some [5]
  | Fam_TiDB, (F_With | F_Recursive) => Some [5; 1]
  | _, _ => None
  end.

Definition supported_in (fam : family) (v : version) (f : feature) : bool :=
  match introduced fam f with Some v0 => version_le v0 v | None => true end.

Definition at_version (d : vsem) (fam : family) (v : version) : vsem :=
  {| vs_name := vs_name d; vs_pred := vs_pred d; vs_symb := vs_symb d; vs_agg := vs_agg d;
     vs_is_null := vs_is_null d; vs_truth := vs_truth d; vs_of_truth := vs_of_truth d; vs_eq3 := vs_eq3 d;
     vs_order := vs_order d; vs_canon := vs_canon d; vs_nulls_smallest := vs_nulls_smallest d;
     vs_supports := fun f => vs_supports d f && supported_in fam v f;
     vs_scalar_first := vs_scalar_first d; vs_pred_error := vs_pred_error d; vs_const := vs_const d;
     vs_truth_error := vs_truth_error d; vs_cmp_coerce := vs_cmp_coerce d; vs_unify := vs_unify d;
     vs_table_fun := vs_table_fun d |}.

(** A version restricts, and never extends, the constructs of the dialect *)
Lemma at_version_sub d fam v f : vs_supports (at_version d fam v) f = true -> vs_supports d f = true.
Proof. simpl. intro H. apply andb_true_iff in H. tauto. Qed.

(** The latest versions accept what the dialect records accept *)
Lemma version_le_refl v : version_le v v = true.
Proof. induction v as [|x v IH]; simpl; [reflexivity|]. rewrite Nat.ltb_irrefl. exact IH. Qed.

Lemma supported_at_intro fam f v0 : introduced fam f = Some v0 -> supported_in fam v0 f = true.
Proof. unfold supported_in. intros ->. apply version_le_refl. Qed.

Definition MySQL57 := at_version MySQL Fam_MySQL [5; 7].
Definition MySQL80 := at_version MySQL Fam_MySQL [8; 0; 30].
Definition MySQL84 := at_version MySQL Fam_MySQL [8; 4].
Definition PostgreSQL12 := at_version PostgreSQL Fam_PostgreSQL [12].
Definition PostgreSQL17 := at_version PostgreSQL Fam_PostgreSQL [17].
Definition SQLite3_24 := at_version SQLite Fam_SQLite [3; 24].
Definition SQLite3_45 := at_version SQLite Fam_SQLite [3; 45].
Definition MariaDB10_4 := at_version MariaDB Fam_MariaDB [10; 4].
Definition MariaDB10_6 := at_version MariaDB Fam_MariaDB [10; 6].
Definition TiDB4 := at_version TiDB Fam_TiDB [4].
