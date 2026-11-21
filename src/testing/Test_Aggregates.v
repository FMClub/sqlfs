(** * Aggregates (TODO 2.5)

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
Notation c1 := (Attr_Z "c1").
Definition xs := values_ [c0] [[int 1]; [int 2]; [int 3]; [int 4]].
Definition pts := values_ [c0; c1] [[int 1; int 1]; [int 2; int 2]; [int 3; int 4]].
Definition kv := values_ [c0; c1] [[str "a"; int 1]; [str "b"; int 2]].
Definition dup := values_ [c0; c1] [[int 1; int 1]; [int 1; int 1]; [int 2; cst NullZ]; [int 2; int 3]].

Definition agg1 (d : vsem) (f : string) (t : squery) (c : scond) : list string :=
  map (fun t => show_value (dot (TD d) t (out_attr 0)))
      (run d (select_where [as_ (fn "cast_string" [agg f (col c0)]) c0] [from_as t [(c0, c0)]] c)).
Definition agg2 (d : vsem) (f : string) (t : squery) : list string :=
  map (fun t => show_value (dot (TD d) t (out_attr 0)))
      (run d (select_where [as_ (fn "cast_string" [agg_x f (col c0) (Some (col c1)) []]) c0] [from_as t [(c0, c0); (c1, c1)]] c_true)).

Example agg_1 : agg1 PostgreSQL "var_pop" xs c_true = ["1.2500000000000000"].
Proof. check. Qed.

Example agg_2 : agg1 PostgreSQL "var_samp" xs c_true = ["1.6666666666666667"].
Proof. check. Qed.

Example agg_3 : agg1 PostgreSQL "stddev" xs c_true = ["1.2909944487358056"].
Proof. check. Qed.

Example agg_4 : agg1 PostgreSQL "stddev_pop" xs c_true = ["1.1180339887498948"].
Proof. check. Qed.

Example agg_5 : agg1 MySQL "variance" xs c_true = ["1.25"].
Proof. check. Qed.

Example agg_6 : agg1 MySQL "stddev" xs c_true = ["1.118033988749895"].
Proof. check. Qed.

Example agg_7 : agg1 MySQL "var_samp" xs c_true = ["1.6666666666666667"].
Proof. check. Qed.

Example agg_8 : agg1 MySQL "stddev_samp" xs c_true = ["1.2909944487358056"].
Proof. check. Qed.

Example agg_9 : agg1 MySQL "bit_xor" xs c_true = ["4"].
Proof. check. Qed.

Example agg_10 : agg1 MySQL "bit_and" xs (c_not c_true) = ["18446744073709551615"].
Proof. check. Qed.

Example agg_11 : agg1 MySQL "bit_or" xs (c_not c_true) = ["0"].
Proof. check. Qed.

Example agg_12 : agg1 PostgreSQL "bit_xor" xs (c_not c_true) = ["NULL"].
Proof. check. Qed.

Example agg_13 : agg1 PostgreSQL "any_value" xs c_true = ["1"].
Proof. check. Qed.

Example agg_14 : agg2 PostgreSQL "corr" pts = ["0.9819805060619657"].
Proof. check. Qed.

Example agg_15 : agg2 PostgreSQL "regr_slope" pts = ["0.6428571428571429"].
Proof. check. Qed.

Example agg_16 : agg2 PostgreSQL "covar_pop" pts = ["1"].
Proof. check. Qed.

Example agg_17 : agg2 PostgreSQL "covar_samp" pts = ["1.5"].
Proof. check. Qed.

Example agg_18 : agg2 PostgreSQL "regr_count" pts = ["3"].
Proof. check. Qed.

Example agg_19 : agg2 PostgreSQL "regr_intercept" pts = ["0.5"].
Proof. check. Qed.

Example agg_20 : agg2 PostgreSQL "regr_r2" pts = ["0.9642857142857143"].
Proof. check. Qed.

Example agg_21 : agg1 MySQL "json_arrayagg" xs c_true = ["[1, 2, 3, 4]"].
Proof. check. Qed.

Example agg_22 : agg1 PostgreSQL "json_agg" xs c_true = ["[1, 2, 3, 4]"].
Proof. check. Qed.

Example agg_23 : agg1 PostgreSQL "jsonb_agg" xs c_true = ["[1, 2, 3, 4]"].
Proof. check. Qed.

Example agg_24 : agg2 PostgreSQL "json_object_agg" kv = ["{ ""a"" : 1, ""b"" : 2 }"].
Proof. check. Qed.

Example agg_25 : agg2 MySQL "json_objectagg" kv = ["{""a"": 1, ""b"": 2}"].
Proof. check. Qed.

Example agg_26 : agg2 MySQL "count_distinct2" dup = ["2"].
Proof. check. Qed.

Example agg_27 : agg1 PostgreSQL "json_agg" xs (c_not c_true) = ["NULL"].
Proof. check. Qed.


(** the variances and the covariances are NaN as soon as an input is NaN or infinite (PostgreSQL regression test
    [aggregates]; TODO 8.11) *)
Definition with_inf := values_ [c0; c1] [[fn "cast_float8" [str "1"]; int 0]; [fn "cast_float8" [str "infinity"]; int 0]].
Example agg_inf_var : agg1 PostgreSQL "var_pop" (values_ [c0] [[fn "cast_float8" [str "1"]]; [fn "cast_float8" [str "infinity"]]]) c_true = ["NaN"].
Proof. check. Qed.
Example agg_inf_sum : agg1 PostgreSQL "sum" (values_ [c0] [[fn "cast_float8" [str "1"]]; [fn "cast_float8" [str "infinity"]]]) c_true = ["Infinity"].
Proof. check. Qed.
Example agg_inf_covar : agg2 PostgreSQL "covar_pop" with_inf = ["NaN"].
Proof. check. Qed.
