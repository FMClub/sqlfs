(** * The names of the output columns (TODO 3.9) *)
Require Import List String ZArith.
Require Import SqlFull Values GenericInstance SqlFullSyntax Naming.
Import ListNotations.
Open Scope string_scope.
Ltac check := vm_compute; reflexivity.

(** PostgreSQL's [FigureColname] *)
Example name_col : pg_colname (col (Attr_Z "t.price")) = "price".
Proof. check. Qed.
Example name_fun : pg_colname (fn "lower" [str "A"]) = "lower".
Proof. check. Qed.
Example name_op : pg_colname (fn "+" [int 1; int 2]) = "?column?".
Proof. check. Qed.
Example name_const : pg_colname (int 1) = "?column?".
Proof. check. Qed.
Example name_count : pg_colname (agg "count(*)" (int 1)) = "count".
Proof. check. Qed.
Example name_sum : pg_colname (agg "sum" (col (Attr_Z "t.x"))) = "sum".
Proof. check. Qed.
Example name_cast : pg_colname (fn "cast_int" [str "1"]) = "int4".
Proof. check. Qed.
Example name_case : pg_colname (e_case c_true (int 1) (int 2)) = "case".
Proof. check. Qed.
