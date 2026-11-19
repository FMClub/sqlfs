(** * Ordered-set and hypothetical-set aggregates (TODO 2.6)

    The functions of the C library ([sqrt], [exp], [ln], [sin], ...) are correctly rounded; the
    [numeric] versions of PostgreSQL have the scale of [numeric.c]. The expected texts are the ones of
    the engines. *)
Require Import List String ZArith NArith.

Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.

Require Import Values TuplesImpl GenericInstance SqlSyntax SqlFullSyntax
        Dialects ValueKit PostgreSQL MySQL SQLite OceanBase SpecRunner.

Import Tuple.
Import ListNotations.
Open Scope string_scope.

Ltac check := vm_compute; reflexivity.

Notation c0 := (Attr_Z "c0").

Definition run (d : vsem) (q : squery) :=
  eval_query_list ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) (to_dialect d q).

Definition text (d : vsem) (e : sexpr) : string :=
  match run d (select_where [as_ (fn "cast_string" [e]) c0] [] c_true) with
  | t :: nil => show_value (dot (TD d) t (out_attr 0))
  | _ => "?"
  end.

Definition fails (d : vsem) (e : sexpr) : bool :=
  match eval_query_result ORN (dialect_of d) (_basesort _ init_db) (_instance _ init_db) 
                          (to_dialect d (select_where [as_ e c0] [] c_true)) with
  | QR_Error _ => true
  | _ => false
  end.

Definition dbl (n : Z) := cst (VFl false n 0).
Definition xs := values_ [c0] [[int 1]; [int 2]; [int 3]; [int 4]; [int 4]; [cst NullZ]].

Definition os (d : vsem) (f : string) (arg : option sexpr) (dir : order_dir) : list string :=
  map (fun t => show_value (dot (TD d) t (out_attr 0)))
      (run d (select_where [as_ (fn "cast_string" [agg_x f (col c0) arg [o_by (col c0) dir]]) c0] [from_as xs [(c0, c0)]] c_true)).

Example os_1 : os PostgreSQL "percentile_cont" (Some (cst (VD 5 1))) Asc = ["3"].
Proof. check. Qed.

Example os_2 : os PostgreSQL "percentile_cont" (Some (cst (VD 25 2))) Asc = ["2"].
Proof. check. Qed.

Example os_3 : os PostgreSQL "percentile_cont" (Some (cst (VD 5 1))) Desc = ["3"].
Proof. check. Qed.

Example os_4 : os PostgreSQL "percentile_disc" (Some (cst (VD 5 1))) Asc = ["3"].
Proof. check. Qed.

Example os_5 : os PostgreSQL "percentile_disc" (Some (cst (VD 0 0))) Asc = ["1"].
Proof. check. Qed.

Example os_6 : os PostgreSQL "mode" None Asc = ["4"].
Proof. check. Qed.

Example os_7 : fails PostgreSQL (agg_x "percentile_cont" (int 1) (Some (cst (VD 15 1))) [o_by (int 1) Asc]) = true.
Proof. check. Qed.

Example os_8 : os PostgreSQL "hyp_rank_asc" (Some (int 3)) Asc = ["3"].
Proof. check. Qed.

Example os_9 : os PostgreSQL "hyp_rank_asc" (Some (int 4)) Asc = ["4"].
Proof. check. Qed.

Example os_10 : os PostgreSQL "hyp_dense_rank_asc" (Some (int 5)) Asc = ["5"].
Proof. check. Qed.

Example os_11 : os PostgreSQL "hyp_rank_desc" (Some (int 3)) Desc = ["4"].
Proof. check. Qed.

Example os_12 : os PostgreSQL "hyp_percent_rank_asc" (Some (int 3)) Asc = ["0.3333333333333333"].
Proof. check. Qed.

Example os_13 : os PostgreSQL "hyp_cume_dist_asc" (Some (int 3)) Asc = ["0.5714285714285714"].
Proof. check. Qed.

Example os_14 : os OceanBaseOracle "percentile_cont" (Some (cst (VD 5 1))) Asc = ["3"].
Proof. check. Qed.

Example os_15 : os OceanBaseOracle "median" None Asc = ["3"].
Proof. check. Qed.

