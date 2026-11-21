(** * The positional semantics and its named view (TODO 6.3)

    [SqlPositional.v]: [SELECT *] over a product keeps every column of every item, also when they have the
    same names, and a derived table may have two columns of the same name; the compiled query of the named
    semantics gives the same rows, read by position ([positional_rows]). *)
Require Import List String ZArith.
Require Import Bool3 FlatData ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.
Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax Dialects MySQL SpecRunner SqlPositional.
Import Tuple.
Import ListNotations.
Open Scope string_scope.

Ltac check := vm_compute; reflexivity.

Notation a := (Attr_Z "a").
Notation b := (Attr_Z "b").
Notation x := (Attr_Z "x").

(** t (a, b): (1, 2), (3, 4) *)
Definition db : db_state :=
  mk_insert (create_table init_db (Rel "t") [a; b]) (Rel "t") [a; b] [[VZ 1; VZ 2]; [VZ 3; VZ 4]].

Notation T := (TD MySQL).
Notation PE := (peval T relname (dialect_of MySQL) (_basesort _ db) (_instance _ db) out_attr).
Notation NAMES := (pnames T relname (_basesort _ db)).
Notation COMPILED q :=
  (map (readat T out_attr 0 (parity T relname (_basesort _ db) q))
       (eval_squery ORN (dialect_of MySQL) (_basesort _ db) (_instance _ db) nil nil
                    (pq_to T relname (_basesort _ db) out_attr q))).

(** [SELECT * FROM t, t]: four columns, two named [a] and two named [b] *)
Definition q_self := PQ_Star T relname [PQ_Table T relname (Rel "t"); PQ_Table T relname (Rel "t")] (PC_True T).

Example self_names : NAMES q_self = [a; b; a; b]. Proof. check. Qed.
Example self_rows : List.length (PE q_self) = 4%nat /\ Forall (fun r => List.length r = 4%nat) (PE q_self).
Proof. split; [check | repeat constructor]. Qed.
Example self_contains : In [VZ 1; VZ 2; VZ 3; VZ 4] (PE q_self). Proof. vm_compute; tauto. Qed.
Example self_named : COMPILED q_self = PE q_self. Proof. check. Qed.

(** [SELECT * FROM (SELECT a AS x, b AS x FROM t)]: a derived table with two columns [x] *)
Definition q_dup :=
  PQ_Star T relname
    [PQ_Select T relname [(x, PE_Col T 0); (x, PE_Col T 1)] [PQ_Table T relname (Rel "t")] (PC_True T)] (PC_True T).

Example dup_names : NAMES q_dup = [x; x]. Proof. check. Qed.
Example dup_contains : In [VZ 3; VZ 4] (PE q_dup). Proof. vm_compute; tauto. Qed.
Example dup_named : COMPILED q_dup = PE q_dup. Proof. check. Qed.

(** [SELECT t.b, t2.a FROM t, t AS t2]: the columns of the second item by position *)
Definition q_pos :=
  PQ_Select T relname [(b, PE_Col T 1); (a, PE_Col T 2)] [PQ_Table T relname (Rel "t"); PQ_Table T relname (Rel "t")] (PC_True T).
Example pos_contains : In [VZ 2; VZ 3] (PE q_pos). Proof. vm_compute; tauto. Qed.
Example pos_named : COMPILED q_pos = PE q_pos. Proof. check. Qed.
