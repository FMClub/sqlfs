(** * The positional view (TODO 6.3) *)
Require Import List String ZArith.
Require Import SqlFull Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax Dialects PostgreSQL MySQL Positional.
Import ListNotations.
Open Scope string_scope.
Ltac check := vm_compute; reflexivity.
Notation a := (Attr_Z "a").
Notation b := (Attr_Z "b").
Definition t := values_ [a; b] [[int 1; int 2]].

(** two columns with the same name: both are kept, in order *)
Example dup_names :
  let r := eval_positional PostgreSQL [("x", col a); ("x", col b)] [from_query t] c_true in
  (pr_names r, map (map NullValues.is_null) (pr_rows r)) = (["x"; "x"], [[false; false]]).
Proof. check. Qed.
Example dup_values :
  pr_rows (eval_positional MySQL [("x", col a); ("x", col b)] [from_query t] c_true) = [[VZ 1; VZ 2]].
Proof. check. Qed.
(** the names of unnamed items: [?column?] twice is allowed *)
Example auto_dup :
  pr_names (eval_positional PostgreSQL (auto_names [fn "+" [col a; int 1]; fn "+" [col b; int 1]]) [from_query t] c_true)
  = ["?column?"; "?column?"].
Proof. check. Qed.
