(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**                       LMF, CNRS & Université Paris-Saclay                       *)
(**                                                                                 *)
(**                        Copyright 2016-2022 : FormalData                         *)
(**                                                                                 *)
(**         Authors: Véronique Benzaken                                             *)
(**                  Évelyne Contejean                                              *)
(**                                                                                 *)
(************************************************************************************)

Require Import Arith NArith ZArith String List Ascii QArith Qcanon Qround Qabs Qminmax DecimalString.
Require Import OrderedSet FiniteSet Bool3 IEEE Temporal Json.

Close Scope Q_scope.
Close Scope Qc_scope.

Definition option_compare (A : Type) (c : A -> A -> comparison) x y :=
  match x, y with
  | Some x, Some y => c x y
  | Some _, None => Gt
  | None, Some _ => Lt
  | None, None => Eq
  end.

Section Sec.

Hypothesis value : Type.
Hypothesis OVal : Oset.Rcd value.

(** Types a.k.a domains in the database textbooks. *)
Inductive type := 
 | type_string 
 | type_Z
 | type_bool
 | type_Q.

Open Scope N_scope.

Definition N_of_type := 
    fun d => 
    match d with   
    | type_string => 0
    | type_Z => 1
    | type_bool => 2
    | type_Q => 3
    end.

Definition OT : Oset.Rcd type.
apply Oemb with N_of_type.
intros d1 d2; case d1; case d2;
(exact (fun _ => refl_equal _) || (intro Abs; discriminate Abs)).
Defined.

Inductive predicate : Type := Predicate : string -> predicate.

Register predicate as datacert.predicate.type.
Register Predicate as datacert.predicate.Predicate.

Definition OP : Oset.Rcd predicate.
split with (fun x y => match x, y with Predicate s1, Predicate s2 => string_compare s1 s2 end).
- intros [s1] [s2]; generalize (Oset.eq_bool_ok Ostring s1 s2); simpl.
  case (string_compare s1 s2).
  + apply f_equal.
  + intros H1 H2; apply H1; injection H2; exact (fun h => h).
  + intros H1 H2; apply H1; injection H2; exact (fun h => h).
- intros [s1] [s2] [s3]; apply (Oset.compare_lt_trans Ostring s1 s2 s3).
- intros [s1] [s2]; apply (Oset.compare_lt_gt Ostring s1 s2).
Defined.

Inductive symbol : Type :=
  | Symbol : string -> symbol
  | CstVal : value -> symbol.

Definition symbol_compare (s1 s2 : symbol) :=
  match s1, s2 with
    | Symbol s1, Symbol s2 => string_compare s1 s2
    | Symbol _, CstVal _ => Lt
    | CstVal _, Symbol _ => Gt
    | CstVal v1, CstVal v2 => Oset.compare OVal v1 v2
  end.

Definition OSymbol : Oset.Rcd symbol.
split with symbol_compare.
- intros [s1 | s1] [s2 | s2]; simpl; try discriminate.
  + generalize (Oset.eq_bool_ok Ostring s1 s2); simpl.
    case (string_compare s1 s2).
    * apply f_equal.
    * intros H1 H2; apply H1; injection H2; exact (fun h => h).
    * intros H1 H2; apply H1; injection H2; exact (fun h => h).
  + generalize (Oset.eq_bool_ok OVal s1 s2); simpl.
    case (Oset.compare OVal s1 s2).
    * apply f_equal.
    * intros H1 H2; apply H1; injection H2; exact (fun h => h).
    * intros H1 H2; apply H1; injection H2; exact (fun h => h).
- intros [s1 | s1] [s2 | s2] [s3 | s3]; simpl;
  try (apply (Oset.compare_lt_trans Ostring) ||
             apply (Oset.compare_lt_trans OVal) ||
             trivial || discriminate).
- intros [s1 | s1] [s2 | s2]; simpl;
  try (apply (Oset.compare_lt_gt Ostring) ||
             apply (Oset.compare_lt_gt OVal) ||
             trivial || discriminate).
Defined.

Inductive aggregate : Type :=
  | Aggregate : string -> aggregate.

Definition OAgg : Oset.Rcd aggregate.
split with (fun x y => match x, y with Aggregate s1, Aggregate s2 => string_compare s1 s2 end).
- intros [s1] [s2]; generalize (Oset.eq_bool_ok Ostring s1 s2); simpl.
  case (string_compare s1 s2).
  + apply f_equal.
  + intros H1 H2; apply H1; injection H2; exact (fun h => h).
  + intros H1 H2; apply H1; injection H2; exact (fun h => h).
- intros [s1] [s2] [s3]; apply (Oset.compare_lt_trans Ostring s1 s2 s3).
- intros [s1] [s2]; apply (Oset.compare_lt_gt Ostring s1 s2).
Defined.

End Sec.


Module NullValues.

(** * Values

    Embedding several coq datatypes (corresponding to SQL domains) into a single
    uniform type for values. Each domain is lifted with [option], [None] being
    the SQL NULL of that domain.

    - [Value_string] : CHAR / VARCHAR / TEXT
    - [Value_Z]      : SMALLINT / INTEGER / BIGINT (unbounded, no overflow)
    - [Value_bool]   : BOOLEAN
    - [Value_Q]      : NUMERIC / DECIMAL / REAL, idealised as exact canonical
                       rationals (no rounding, no overflow)
    - [Value_D]      : an exact decimal number [(q, f, s)]: its value [q], the number [f] of
                       decimal digits which the engine holds (it can exceed [s], as in the
                       quotients of MySQL), and its scale [s], the number of decimals it is
                       displayed with ([1.50] is [(3/2, 2, 2)])
    - [Value_F]      : a binary floating-point number [(x, k)]: its exact value [x] (a number of the
                       format, 0 for the special values), and [k = 2 * tag + w], where [tag] is
                       finite, -0, +inf, -inf or NaN ([IEEE.v]) and [w] is 1 for binary32
                       ([REAL] of PostgreSQL, [FLOAT] of MySQL), 0 for binary64
    - [Value_I]      : an integer of a narrower or unsigned type [(z, w)]: [w] is 16 or 32 for the
                       [smallint] and [integer] of PostgreSQL, 1 for the [BIGINT UNSIGNED] of MySQL
                       (a [Value_Z] is a [bigint], [BIGINT])
    - [Value_C]      : a string with an explicit collation ([s COLLATE c]): the string and the
                       name of the collation
    - [Value_T]      : a date or a time [(n, k)]: [k] is 0 for a [DATE] ([n] days from 1970-01-01),
                       1 for a [TIME] ([n] microseconds), 2 for a [TIMESTAMP] / [DATETIME] without
                       time zone and 3 for a [TIMESTAMP WITH TIME ZONE] ([n] microseconds from
                       1970-01-01 00:00:00, UTC for the latter), plus 10 times the number of
                       fractional digits to display ([Temporal.v])
    - [Value_V]      : an interval [(months, days, microseconds)] (PostgreSQL)
    - [Value_J]      : a JSON value [(t, k)]: its compact text [t] ([Json.v]); [k] is 0 for a value
                       whose objects are normalized (MySQL [JSON], PostgreSQL [jsonb]), 1 for a
                       PostgreSQL [json], which keeps its text
    - [Value_Err]    : the failure of an evaluation (division by zero in PostgreSQL,
                       an invalid conversion, ...), with the kind of the error. It
                       belongs to no SQL domain: a query whose evaluation produces it
                       fails (see [eval_query_result] in [SqlFull.v]).
*)
Inductive value : Set :=
  | Value_string : option string -> value
  | Value_Z : option Z -> value
  | Value_bool : option bool -> value
  | Value_Q : option Qc -> value
  | Value_Err : string -> value
  | Value_D : option (Qc * nat * nat) -> value
  | Value_F : option (Qc * nat) -> value
  | Value_I : option (Z * nat) -> value
  | Value_C : option (string * string) -> value
  | Value_T : option (Z * nat) -> value
  | Value_V : option (Z * Z * Z) -> value
  | Value_J : option (string * nat) -> value.

Register value as datacert.value.type.
Register Value_string as datacert.value.Value_string.
Register Value_Z as datacert.value.Value_Z.
Register Value_bool as datacert.value.Value_bool.

Definition type_of_value v := 
match v with
  | Value_string _  => type_string
  | Value_Z _ => type_Z
  | Value_bool _ => type_bool
  | Value_Q _ => type_Q
  | Value_Err _ => type_Z
  | Value_D _ => type_Q
  | Value_F _ => type_Q
  | Value_I _ => type_Z
  | Value_C _ => type_string
  | Value_T _ => type_Z
  | Value_V _ => type_Z
  | Value_J _ => type_string
  end.

(** Default values for each type: the NULL of that type. *)
Definition default_value d :=
  match d with
    | type_string => Value_string None
    | type_Z => Value_Z None
    | type_bool => Value_bool None
    | type_Q => Value_Q None
  end.

Definition is_null v :=
  match v with
  | Value_string None | Value_Z None | Value_bool None | Value_Q None | Value_D None | Value_F None 
  | Value_I None | Value_C None | Value_T None | Value_V None | Value_J None => true
  | _ => false
  end.

(** Comparison over values, in order to build an ordered type over values, and then
    finite sets. This is the _structural_ order used for grouping, DISTINCT and set
    operations (where two NULLs are not distinct); it is not the SQL comparison
    predicate, see [sql_compare] below.
*)

Definition OQc : Oset.Rcd Qc.
split with Qccompare.
- intros a1 a2; case_eq (Qccompare a1 a2); intro H.
  + apply Qceq_alt; assumption.
  + intro K; subst a2.
    rewrite (proj1 (Qceq_alt a1 a1) (refl_equal _)) in H; discriminate H.
  + intro K; subst a2.
    rewrite (proj1 (Qceq_alt a1 a1) (refl_equal _)) in H; discriminate H.
- intros a1 a2 a3 H12 H23.
  apply Qclt_alt; apply Qclt_trans with a2; apply Qclt_alt; assumption.
- intros a1 a2; unfold Qccompare; rewrite Qcompare_antisym; apply refl_equal.
Defined.

Definition ODec : Oset.Rcd (Qc * nat * nat) := mk_opairs (mk_opairs OQc Onat) Onat.
Definition OFlt : Oset.Rcd (Qc * nat) := mk_opairs OQc Onat.
Definition OInt : Oset.Rcd (Z * nat) := mk_opairs OZ Onat.
Definition OColl : Oset.Rcd (string * string) := mk_opairs Ostring Ostring.
Definition OIntv : Oset.Rcd (Z * Z * Z) := mk_opairs (mk_opairs OZ OZ) OZ.
Definition OJson : Oset.Rcd (string * nat) := mk_opairs Ostring Onat.

Definition value_rank v : N :=
  match v with
  | Value_string _ => 0%N
  | Value_Z _ => 1%N
  | Value_bool _ => 2%N
  | Value_Q _ => 3%N
  | Value_Err _ => 4%N
  | Value_D _ => 5%N
  | Value_F _ => 6%N
  | Value_I _ => 7%N
  | Value_C _ => 8%N
  | Value_T _ => 9%N
  | Value_V _ => 10%N
  | Value_J _ => 11%N
  end.

Definition value_compare x y :=
  match x, y with
    | Value_string s1, Value_string s2 => option_compare _ string_compare s1 s2
    | Value_Z z1, Value_Z z2 => option_compare _ Z.compare z1 z2
    | Value_bool b1, Value_bool b2 => option_compare _ bool_compare b1 b2
    | Value_Q q1, Value_Q q2 => option_compare _ Qccompare q1 q2
    | Value_Err e1, Value_Err e2 => string_compare e1 e2
    | Value_D d1, Value_D d2 => option_compare _ (Oset.compare ODec) d1 d2
    | Value_F d1, Value_F d2 => option_compare _ (Oset.compare OFlt) d1 d2
    | Value_I d1, Value_I d2 => option_compare _ (Oset.compare OInt) d1 d2
    | Value_C d1, Value_C d2 => option_compare _ (Oset.compare OColl) d1 d2
    | Value_T d1, Value_T d2 => option_compare _ (Oset.compare OInt) d1 d2
    | Value_V d1, Value_V d2 => option_compare _ (Oset.compare OIntv) d1 d2
    | Value_J d1, Value_J d2 => option_compare _ (Oset.compare OJson) d1 d2
    | _, _ => N.compare (value_rank x) (value_rank y)
  end.

Definition OVal : Oset.Rcd value.
split with value_compare.
- (* 1/3 *)
  intros [[s1 | ] | [z1 | ] | [b1 | ] | [q1 | ] | e1 | [d1 | ] | [f1 | ] | [i1 | ] | [k1 | ] | [t1 | ] | [v1 | ] | [j1 | ]] [[s2 | ] | [z2 | ] | [b2 | ] | [q2 | ] | e2 | [d2 | ] | [f2 | ] | [i2 | ] | [k2 | ] | [t2 | ] | [v2 | ] | [j2 | ]];
    simpl; try discriminate; trivial.
  + generalize (Oset.eq_bool_ok Ostring s1 s2); simpl; case (string_compare s1 s2).
    * apply (f_equal (fun x => Value_string (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok OZ z1 z2); simpl; case (Z.compare z1 z2).
    * apply (f_equal (fun x => Value_Z (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok Obool b1 b2); simpl; case (bool_compare b1 b2).
    * apply (f_equal (fun x => Value_bool (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok OQc q1 q2); simpl; case (Qccompare q1 q2).
    * apply (f_equal (fun x => Value_Q (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok Ostring e1 e2); simpl; case (string_compare e1 e2).
    * apply (f_equal (fun x => Value_Err x)).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok ODec d1 d2); unfold Oset.eq_bool; simpl;
    destruct (compareAB (compareAB Qccompare Nat.compare) Nat.compare d1 d2).
    * apply (f_equal (fun x => Value_D (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok OFlt f1 f2); unfold Oset.eq_bool; simpl;
    destruct (compareAB Qccompare Nat.compare f1 f2).
    * apply (f_equal (fun x => Value_F (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok OInt i1 i2); unfold Oset.eq_bool; simpl;
    destruct (compareAB Z.compare Nat.compare i1 i2).
    * apply (f_equal (fun x => Value_I (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok OColl k1 k2); unfold Oset.eq_bool; simpl;
    destruct (compareAB string_compare string_compare k1 k2).
    * apply (f_equal (fun x => Value_C (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok OInt t1 t2); unfold Oset.eq_bool; simpl;
    destruct (compareAB Z.compare Nat.compare t1 t2).
    * apply (f_equal (fun x => Value_T (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok OIntv v1 v2); unfold Oset.eq_bool; simpl;
    destruct (compareAB (compareAB Z.compare Z.compare) Z.compare v1 v2).
    * apply (f_equal (fun x => Value_V (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok OJson j1 j2); unfold Oset.eq_bool; simpl;
    destruct (compareAB string_compare Nat.compare j1 j2).
    * apply (f_equal (fun x => Value_J (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
- (* 1/2 *)
  intros [[s1 | ] | [z1 | ] | [b1 | ] | [q1 | ] | e1 | [d1 | ] | [f1 | ] | [i1 | ] | [k1 | ] | [t1 | ] | [v1 | ] | [j1 | ]] [[s2 | ] | [z2 | ] | [b2 | ] | [q2 | ] | e2 | [d2 | ] | [f2 | ] | [i2 | ] | [k2 | ] | [t2 | ] | [v2 | ] | [j2 | ]]
         [[s3 | ] | [z3 | ] | [b3 | ] | [q3 | ] | e3 | [d3 | ] | [f3 | ] | [i3 | ] | [k3 | ] | [t3 | ] | [v3 | ] | [j3 | ]]; simpl; trivial; try discriminate.
  + apply (Oset.compare_lt_trans Ostring).
  + apply (Oset.compare_lt_trans OZ).
  + apply (Oset.compare_lt_trans Obool).
  + apply (Oset.compare_lt_trans OQc).
  + apply (Oset.compare_lt_trans Ostring).
  + apply (Oset.compare_lt_trans ODec).
  + apply (Oset.compare_lt_trans OFlt).
  + apply (Oset.compare_lt_trans OInt).
  + apply (Oset.compare_lt_trans OColl).
  + apply (Oset.compare_lt_trans OInt).
  + apply (Oset.compare_lt_trans OIntv).
  + apply (Oset.compare_lt_trans OJson).
- (* 1/1 *)
  intros [[s1 | ] | [z1 | ] | [b1 | ] | [q1 | ] | e1 | [d1 | ] | [f1 | ] | [i1 | ] | [k1 | ] | [t1 | ] | [v1 | ] | [j1 | ]] [[s2 | ] | [z2 | ] | [b2 | ] | [q2 | ] | e2 | [d2 | ] | [f2 | ] | [i2 | ] | [k2 | ] | [t2 | ] | [v2 | ] | [j2 | ]];
    simpl; trivial.
  + apply (Oset.compare_lt_gt Ostring).
  + apply (Oset.compare_lt_gt OZ).
  + apply (Oset.compare_lt_gt Obool).
  + apply (Oset.compare_lt_gt OQc).
  + apply (Oset.compare_lt_gt Ostring).
  + apply (Oset.compare_lt_gt ODec).
  + apply (Oset.compare_lt_gt OFlt).
  + apply (Oset.compare_lt_gt OInt).
  + apply (Oset.compare_lt_gt OColl).
  + apply (Oset.compare_lt_gt OInt).
  + apply (Oset.compare_lt_gt OIntv).
  + apply (Oset.compare_lt_gt OJson).
Defined.

Definition FVal := Fset.build OVal.

Definition value_eqb v1 v2 :=
  match value_compare v1 v2 with Eq => true | _ => false end.

(** * Truth values as values, and conversely *)

Definition value_of_bool3 (b : bool3) :=
  match b with
  | true3 => Value_bool (Some true)
  | false3 => Value_bool (Some false)
  | unknown3 => Value_bool None
  end.

(** A value used as a condition: anything which is not TRUE or FALSE is UNKNOWN. *)
Definition bool3_of_value v :=
  match v with
  | Value_bool (Some true) => true3
  | Value_bool (Some false) => false3
  | _ => unknown3
  end.

Definition bool3_of_bool (b : bool) := if b then true3 else false3.

Definition andb3 := Bool.andb Bool3.
Definition orb3 := Bool.orb Bool3.
Definition negb3 := Bool.negb Bool3.

(** * The numeric tower: integers are implicitly promoted to rationals. *)

Inductive num : Set :=
  | Num_Z : Z -> num
  | Num_Q : Qc -> num.

Definition Qc_of_Z (z : Z) : Qc := Q2Qc (inject_Z z).

Definition Qc_of_num n := match n with Num_Z z => Qc_of_Z z | Num_Q q => q end.

Definition num_of_value v :=
  match v with
  | Value_Z (Some z) => Some (Num_Z z)
  | Value_Q (Some q) => Some (Num_Q q)
  | Value_D (Some (q, _, _)) => Some (Num_Q q)
  (* a finite float or a negative zero *)
  | Value_F (Some (q, k)) => if Nat.leb (Nat.div (Nat.modulo k 10) 2) 1 then Some (Num_Q q) else None
  | Value_I (Some (z, _)) => Some (Num_Z z)
  | _ => None
  end.

Definition value_of_num n :=
  match n with Num_Z z => Value_Z (Some z) | Num_Q q => Value_Q (Some q) end.

Definition is_Q v := match v with Value_Q _ | Value_D _ => true | _ => false end.

(** The NULL resulting from an arithmetic operation over [l]: numeric as soon as
    one of the arguments is numeric, integer otherwise. *)
Definition null_num (l : list value) :=
  if existsb is_Q l then Value_Q None else Value_Z None.

(** Binary arithmetic. [fz] and [fq] are partial: [None] models a runtime error
    (e.g. division by zero), which this total semantics maps to NULL. *)
Definition arith2 (fz : Z -> Z -> option Z) (fq : Qc -> Qc -> option Qc) (l : list value) :=
  match l with
  | v1 :: v2 :: nil =>
    match num_of_value v1, num_of_value v2 with
    | Some (Num_Z a), Some (Num_Z b) => Value_Z (fz a b)
    | Some a, Some b => Value_Q (fq (Qc_of_num a) (Qc_of_num b))
    | _, _ => null_num l
    end
  | _ => null_num l
  end.

Definition arith1 (fz : Z -> option Z) (fq : Qc -> option Qc) (l : list value) :=
  match l with
  | v1 :: nil =>
    match num_of_value v1 with
    | Some (Num_Z a) => Value_Z (fz a)
    | Some (Num_Q a) => Value_Q (fq a)
    | None => null_num l
    end
  | _ => null_num l
  end.

Definition Qc_is_zero (q : Qc) := match Qccompare q (Qc_of_Z 0) with Eq => true | _ => false end.

Definition Qc_floor (q : Qc) : Z := Qfloor q.
Definition Qc_ceiling (q : Qc) : Z := Qceiling q.
(** truncation towards zero *)
(** the number which a value stands for, if it is a number *)
Definition rat_of_value (v : value) : option Q :=
  match v with
  | Value_Z (Some z) => Some (inject_Z z)
  | Value_Q (Some q) => Some (this q)
  | Value_D (Some (q, _, _)) => Some (this q)
  | Value_I (Some (z, _)) => Some (inject_Z z)
  | Value_F (Some (q, k)) => if Nat.leb (Nat.div (Nat.modulo k 10) 2) 1 then Some (this q) else None
  (* a date is its number of days, a time or a timestamp its number of microseconds: the key of a [RANGE]
     frame whose offset is an interval expressed in that unit (TODO 3.1) *)
  | Value_T (Some (n, _)) => Some (inject_Z n)
  | _ => None
  end.

Definition value_of_rat (q : Q) : value := Value_Q (Some (Q2Qc q)).

Definition is_err (v : value) : bool := match v with Value_Err _ => true | _ => false end.

(** The functions which do not evaluate all their arguments: [COALESCE] and its variants stop at
    the first non-NULL argument, the conditional functions evaluate one branch. *)
Definition lazy_names : list string :=
  ("coalesce" :: "ifnull" :: "nvl" :: "nvl2" :: "if" :: "iif" :: "case" :: "decode" :: nil)%string.

Definition is_lazy_symbol (f : symbol value) : bool :=
  match f with
  | Symbol _ s => existsb (String.eqb s) lazy_names
  | CstVal _ _ => false
  end.

Definition Qc_trunc (q : Qc) : Z := Z.quot (Qnum q) (Zpos (Qden q)).
(** rounding to the nearest integer, ties away from zero *)
Definition Qc_round (q : Qc) : Z :=
  match Qccompare q (Qc_of_Z 0) with
  | Lt => Z.opp (Qfloor (Qplus (Qopp q) (1 # 2)))
  | _ => Qfloor (Qplus q (1 # 2))
  end.

(** The exact powers are computed for exponents up to [power_bound]; beyond, the result is not computed
    (None), except for the bases 0, 1 and -1: an exact power with a huge exponent does not fit in memory, and
    the engines compute it approximately (PostgreSQL: [power_var], with a limited precision) *)
Definition power_bound : Z := 4096.
Definition trivial_base (a : Z) : bool := Z.eqb a 0 || Z.eqb a 1 || Z.eqb a (-1).

Definition Zpower_opt (a b : Z) : option Z :=
  match b with
  | Zneg _ => None
  | _ => if Z.ltb power_bound b && negb (trivial_base a)
         then None
         else if trivial_base a && Z.ltb power_bound b
         then Some (if Z.eqb a (-1) then (if Z.even b then 1 else -1) else a)
         else Some (Z.pow a b)
  end.

Definition Qcpower_opt (a b : Qc) : option Qc :=
  (* only integral exponents are supported, up to [power_bound] (1 and -1 to any exponent) *)
  if negb (Pos.eqb (Qden b) 1) then None
  else if Z.ltb power_bound (Z.abs (Qnum b))
  then (if Pos.eqb (Qden a) 1 && Z.eqb (Qnum a) 1 then Some (Qc_of_Z 1)
        else if Pos.eqb (Qden a) 1 && Z.eqb (Qnum a) (-1) then Some (Qc_of_Z (if Z.even (Qnum b) then 1 else -1))
        else None)
  else match Qnum b with
       | Z0 => Some (Qc_of_Z 1)
       | Zpos p => Some (Qcpower a (Pos.to_nat p))
       | Zneg p => if Qc_is_zero a then None else Some (Qcinv (Qcpower a (Pos.to_nat p)))
       end.

(** * SQL comparison

    [sql_compare v1 v2] is [None] when one of the arguments is NULL, or when the
    two values are not comparable (a typing error in SQL); the comparison
    predicates are then UNKNOWN. *)
(** * Dates and times: the values *)

Definition VDate (days : Z) : value := Value_T (Some (days, 0%nat)).
Definition VTime (us : Z) (fsp : nat) : value := Value_T (Some (us, (1 + 10 * fsp)%nat)).
Definition VTs (ts : Z) (fsp : nat) : value := Value_T (Some (ts, (2 + 10 * fsp)%nat)).
Definition VTsTz (ts : Z) (fsp : nat) : value := Value_T (Some (ts, (3 + 10 * fsp)%nat)).
Definition VIntv (mo d us : Z) : value := Value_V (Some (mo, d, us)).

(** the kind (0 date, 1 time, 2 timestamp, 3 timestamp with time zone), the number and the fractional digits *)
Definition temporal_parts (v : value) : option (nat * Z * nat) :=
  match v with
  | Value_T (Some (n, k)) => Some (Nat.modulo k 10, n, Nat.div k 10)
  | _ => None
  end.

(** a date or a timestamp, as microseconds from the epoch *)
Definition to_ts (v : value) : option Z :=
  match temporal_parts v with
  | Some (0%nat, d, _) => Some (ts_of d 0)
  | Some (2%nat, t, _) | Some (3%nat, t, _) => Some t
  | _ => None
  end.

(** the length of an interval, a month being 30 days ([interval_cmp_value]) *)
Definition interval_usec (iv : Z * Z * Z) : Z :=
  let '(mo, d, us) := iv in (mo * 30 + d) * usec_per_day + us.

(** a string read as a value of the kind of [like] (the literals of unknown type of PostgreSQL, the
    conversion of strings in the comparisons of MySQL) *)
Definition parse_like (like : value) (t : string) : option value :=
  match temporal_parts like with
  | Some (0%nat, _, _) => match parse_date t with Some d => Some (VDate d) | None => None end
  | Some (1%nat, _, f) => match parse_time t with Some u => Some (VTime u f) | None => None end
  | Some (2%nat, _, f) => match parse_timestamp t with Some u => Some (VTs u f) | None => None end
  | Some (3%nat, _, f) => match parse_timestamp t with Some u => Some (VTsTz u f) | None => None end
  | _ => None
  end.

Definition pg_temporal_text (v : value) : option string :=
  match v, temporal_parts v with
  | _, Some (0%nat, d, _) => Some (date_text d)
  | _, Some (1%nat, u, _) => Some (pg_time_text u)
  | _, Some (2%nat, t, _) => Some (pg_timestamp_text t)
  | _, Some (_, t, _) => Some (pg_timestamp_text t ++ "+00")
  | Value_V (Some (mo, d, us)), _ => Some (pg_interval_text mo d us)
  | _, _ => None
  end.

Definition temporal_compare (v1 v2 : value) : option comparison :=
  match v1, v2 with
  | Value_V (Some a), Value_V (Some b) => Some (Z.compare (interval_usec a) (interval_usec b))
  | Value_T (Some _), Value_T (Some _) =>
    match temporal_parts v1, temporal_parts v2 with
    | Some (1%nat, a, _), Some (1%nat, b, _) => Some (Z.compare a b)
    | _, _ => match to_ts v1, to_ts v2 with Some a, Some b => Some (Z.compare a b) | _, _ => None end
    end
  | _, _ => None
  end.

(** The order of the floats of PostgreSQL ([float8_cmp_internal]): -Infinity < the numbers < Infinity < NaN,
    and NaN is equal to NaN. *)
Definition float_rank (v : value) : option nat :=
  match v with
  | Value_F (Some (_, k)) => 
    match Nat.div (Nat.modulo k 10) 2 with 2%nat => Some 2%nat | 3%nat => Some 0%nat | 4%nat => Some 3%nat | _ => Some 1%nat end
  | Value_Z (Some _) | Value_Q (Some _) | Value_D (Some _) | Value_I (Some _) => Some 1%nat
  | _ => None
  end.

(** ** Arrays (PostgreSQL, TODO 2.8): a [Value_J] of kind 2 holds the JSON array of the elements. Two
    arrays compare element by element, a NULL element being greater than the others, a shorter array
    which is a prefix being smaller ([array_cmp]). *)
Fixpoint dec_digits (l : list ascii) (acc : Z) (scale : nat) (dot : bool) : option (Z * nat) :=
  match l with
  | nil => Some (acc, scale)
  | c :: r => if Ascii.eqb c "."%char then (if dot then None else dec_digits r acc scale true)
              else let n := Z.of_nat (nat_of_ascii c) in
                   if (Z.leb 48 n && Z.leb n 57)%bool
                   then dec_digits r (acc * 10 + (n - 48))%Z (if dot then S scale else scale) dot
                   else None
  end.

Definition json_num_qc (t : string) : option Qc :=
  let (neg, l) := match list_ascii_of_string t with "-"%char :: r => (true, r) | l => (false, l) end in
  match dec_digits l 0%Z 0%nat false with
  | Some (m, sc) => let q := Qcdiv (Qc_of_Z m) (Qc_of_Z (Z.pow 10 (Z.of_nat sc))) in
                    Some (if neg then Qcopp q else q)
  | None => None
  end.

Definition jelem_compare (a b : json) : comparison :=
  match a, b with
  | JNull, JNull => Eq
  | JNull, _ => Gt
  | _, JNull => Lt
  | JNum x, JNum y => match json_num_qc x, json_num_qc y with Some p, Some q => Qccompare p q | _, _ => string_compare x y end
  | JStr x, JStr y => string_compare x y
  | JBool x, JBool y => bool_compare x y
  | _, _ => string_compare (text_compact a) (text_compact b)
  end.

Fixpoint jlist_compare (a b : list json) : comparison :=
  match a, b with
  | nil, nil => Eq
  | nil, _ => Lt
  | _, nil => Gt
  | x :: a', y :: b' => match jelem_compare x y with Eq => jlist_compare a' b' | c => c end
  end.

Definition sql_compare v1 v2 : option comparison :=
  match v1, v2 with
  | Value_T (Some _), Value_T (Some _) | Value_V (Some _), Value_V (Some _) => temporal_compare v1 v2
  | Value_J (Some (a, 2%nat)), Value_J (Some (b, 2%nat)) =>
    match parse_json a, parse_json b with
    | Some (JArr x), Some (JArr y) => Some (jlist_compare x y)
    | _, _ => Some (string_compare a b)
    end
  | Value_J (Some (a, _)), Value_J (Some (b, _)) => Some (string_compare a b)
  | Value_T (Some _), Value_string (Some t) => 
    match parse_like v1 t with Some w => temporal_compare v1 w | None => None end
  | Value_string (Some t), Value_T (Some _) => 
    match parse_like v2 t with Some w => temporal_compare w v2 | None => None end
  | Value_string (Some s1), Value_string (Some s2) => Some (string_compare s1 s2)
  | Value_bool (Some b1), Value_bool (Some b2) => Some (bool_compare b1 b2)
  | _, _ =>
    match float_rank v1, float_rank v2 with
    | Some r1, Some r2 =>
      if negb (Nat.eqb r1 1) || negb (Nat.eqb r2 1) then Some (Nat.compare r1 r2)
      else match num_of_value v1, num_of_value v2 with
           | Some (Num_Z a), Some (Num_Z b) => Some (Z.compare a b)
           | Some a, Some b => Some (Qccompare (Qc_of_num a) (Qc_of_num b))
           | _, _ => None
           end
    | _, _ => None
    end
  end.

Definition cmp3 (test : comparison -> bool) v1 v2 :=
  match sql_compare v1 v2 with
  | Some c => bool3_of_bool (test c)
  | None => unknown3
  end.

Definition is_Eq c := match c with Eq => true | _ => false end.
Definition is_Lt c := match c with Lt => true | _ => false end.
Definition is_Gt c := match c with Gt => true | _ => false end.

Definition sql_eq3 := cmp3 is_Eq.
Definition sql_lt3 := cmp3 is_Lt.
Definition sql_le3 := cmp3 (fun c => negb (is_Gt c)).

(** The total order used by ORDER BY, MIN and MAX on non-NULL values: the SQL
    comparison when it is defined, the structural order otherwise. *)
Definition sql_order v1 v2 : comparison :=
  match sql_compare v1 v2 with
  | Some c => c
  | None => value_compare v1 v2
  end.

(** IS NOT DISTINCT FROM: NULL-safe equality, never UNKNOWN. *)
Definition not_distinct v1 v2 :=
  match is_null v1, is_null v2 with
  | true, true => true
  | false, false => match sql_compare v1 v2 with Some Eq => true | _ => false end
  | _, _ => false
  end.

Definition binary3 (f : value -> value -> bool3) (l : list value) :=
  match l with
  | v1 :: v2 :: nil => f v1 v2
  | _ => unknown3
  end.

Definition unary3 (f : value -> bool3) (l : list value) :=
  match l with
  | v1 :: nil => f v1
  | _ => unknown3
  end.

(** Row-wise equality [(a1, ..., an) = (b1, ..., bn)], the arguments being given
    as [a1 :: ... :: an :: b1 :: ... :: bn :: nil]. *)
Fixpoint row_eq3 (l1 l2 : list value) :=
  match l1, l2 with
  | nil, nil => true3
  | v1 :: l1, v2 :: l2 => andb3 (sql_eq3 v1 v2) (row_eq3 l1 l2)
  | _, _ => unknown3
  end.

Definition split_half (l : list value) :=
  let n := Nat.div2 (List.length l) in (firstn n l, skipn n l).

(** [x IN (v1, ..., vn)] *)
Definition in_list3 (l : list value) :=
  match l with
  | nil => unknown3
  | x :: l => fold_left (fun acc v => orb3 acc (sql_eq3 x v)) l false3
  end.

(** * Strings *)

Open Scope string_scope.

(** LIKE patterns: [%] matches any sequence of characters, [_] any single
    character, and a backslash escapes the next character of the pattern. *)
Fixpoint like_match (p : string) : string -> bool :=
  match p with
  | EmptyString => fun s => match s with EmptyString => true | _ => false end
  | String "%" p' =>
    fix star (s : string) : bool :=
      like_match p' s || match s with EmptyString => false | String _ s' => star s' end
  | String "_" p' =>
    fun s => match s with EmptyString => false | String _ s' => like_match p' s' end
  | String "\" (String c p') =>
    fun s => match s with
             | EmptyString => false
             | String c' s' => Ascii.eqb c c' && like_match p' s'
             end
  | String c p' =>
    fun s => match s with
             | EmptyString => false
             | String c' s' => Ascii.eqb c c' && like_match p' s'
             end
  end.

Definition like3 v p :=
  match v, p with
  | Value_string (Some s), Value_string (Some p) => bool3_of_bool (like_match p s)
  | _, _ => unknown3
  end.

Definition upper_ascii (c : ascii) :=
  let n := nat_of_ascii c in
  if Nat.leb 97 n && Nat.leb n 122 then ascii_of_nat (n - 32) else c.

Definition lower_ascii (c : ascii) :=
  let n := nat_of_ascii c in
  if Nat.leb 65 n && Nat.leb n 90 then ascii_of_nat (n + 32) else c.

Fixpoint string_map (f : ascii -> ascii) (s : string) :=
  match s with
  | EmptyString => EmptyString
  | String c s => String (f c) (string_map f s)
  end.

Fixpoint string_rev_aux (s acc : string) :=
  match s with
  | EmptyString => acc
  | String c s => string_rev_aux s (String c acc)
  end.

Definition string_rev s := string_rev_aux s EmptyString.

Fixpoint string_ltrim (s : string) :=
  match s with
  | String " " s' => string_ltrim s'
  | _ => s
  end.

Definition string_rtrim s := string_rev (string_ltrim (string_rev s)).

Fixpoint string_replace_aux (n : nat) (from to s : string) :=
  match n with
  | O => s
  | S n =>
    match s with
    | EmptyString => EmptyString
    | String c s' =>
      if String.prefix from s
      then to ++ string_replace_aux n from to
                   (String.substring (String.length from)
                                     (String.length s - String.length from) s)
      else String c (string_replace_aux n from to s')
    end
  end.

Definition string_replace (s from to : string) :=
  match from with
  | EmptyString => s
  | _ => string_replace_aux (S (String.length s)) from to s
  end.

Fixpoint string_repeat (n : nat) (s : string) :=
  match n with
  | O => EmptyString
  | S n => s ++ string_repeat n s
  end.

(** SUBSTRING (s FROM start FOR len), 1-based as in SQL. *)
Definition sql_substring (s : string) (start : Z) (len : option Z) :=
  let total := Z.of_nat (String.length s) in
  let stop := match len with
              | Some l => (start + l)%Z
              | None => (total + 1)%Z
              end in
  let start' := Z.max start 1 in
  let stop' := Z.min stop (total + 1)%Z in
  if (stop' <=? start')%Z
  then EmptyString
  else String.substring (Z.to_nat (start' - 1)) (Z.to_nat (stop' - start')) s.

Definition string_of_Z (z : Z) : string := NilZero.string_of_int (Z.to_int z).

Definition Z_of_string (s : string) : option Z :=
  match s with
  | EmptyString | String "-" EmptyString => None
  | _ => match NilZero.int_of_string s with
         | Some i => Some (Z.of_int i)
         | None => None
         end
  end.

Definition string_of_Qc (q : Qc) : string :=
  if Pos.eqb (Qden q) 1
  then string_of_Z (Qnum q)
  else string_of_Z (Qnum q) ++ "/" ++ string_of_Z (Zpos (Qden q)).

(** Decimal literals: [-]digits[.digits] *)
Definition Qc_of_string (s : string) : option Qc :=
  match String.index 0 "." s with
  | None => match Z_of_string s with Some z => Some (Qc_of_Z z) | None => None end
  | Some i =>
    let ip := String.substring 0 i s in
    let fp := String.substring (S i) (String.length s - S i) s in
    let neg := String.prefix "-" ip in
    let ip' := match ip with
               | EmptyString => Some 0%Z
               | String "-" EmptyString => Some 0%Z
               | _ => Z_of_string ip
               end in
    match ip', fp with
    | Some a, EmptyString => Some (Qc_of_Z a)
    | Some a, _ =>
      match NilZero.uint_of_string fp with
      | Some u =>
        let den := Z.pow 10 (Z.of_nat (String.length fp)) in
        let frac := Z.of_uint u in
        let n := (Z.abs a * den + frac)%Z in
        Some (Q2Qc (Qmake (if neg then Z.opp n else n) (Z.to_pos den)))
      | None => None
      end
    | None, _ => None
    end
  end.

Definition bool_of_string (s : string) : option bool :=
  let s := string_map lower_ascii s in
  if (String.eqb s "true" || String.eqb s "t" || String.eqb s "yes" || String.eqb s "1")%bool
  then Some true
  else if (String.eqb s "false" || String.eqb s "f" || String.eqb s "no" || String.eqb s "0")%bool
       then Some false
       else None.

(** * Integers of fixed width

    A [Value_Z] is a 64-bit integer ([bigint], [BIGINT]); a [Value_I (z, w)] an integer of width
    [w] (16, 32) or an unsigned 64-bit integer ([w] = 1, MySQL). *)
Definition int_parts (v : value) : option (Z * nat) :=
  match v with
  | Value_Z (Some z) => Some (z, 64%nat)
  | Value_I (Some (z, w)) => Some (z, w)
  | _ => None
  end.

Definition int_range_ok (w : nat) (z : Z) : bool :=
  match w with
  | 16%nat => (Z.leb (-32768) z && Z.leb z 32767)%bool
  | 32%nat => (Z.leb (-2147483648) z && Z.leb z 2147483647)%bool
  | 1%nat => (Z.leb 0 z && Z.leb z 18446744073709551615)%bool
  | _ => (Z.leb (-9223372036854775808) z && Z.leb z 9223372036854775807)%bool
  end.

Definition VInt (w : nat) (z : Z) : value := if Nat.eqb w 64 then Value_Z (Some z) else Value_I (Some (z, w)).

(** [Value_I] as a [Value_Z], for the functions which do not depend on the width *)
Definition widen (v : value) : value :=
  match v with Value_I (Some (z, _)) => Value_Z (Some z) | Value_I None => Value_Z None | _ => v end.

(** The integer arithmetic of PostgreSQL ([int.c], [int8.c]): the result has the wider type of
    the operands, and a result out of its range is an error ([smallint out of range], ...). *)
Definition pg_int_error (w : nat) : value :=
  Value_Err (match w with 16%nat => "smallint out of range" | 32%nat => "integer out of range" | _ => "bigint out of range" end).

Definition pg_int2 (f : Z -> Z -> Z) (old : list value -> value) (l : list value) : value :=
  match l with
  | v1 :: v2 :: nil =>
    match int_parts v1, int_parts v2 with
    | Some (a, w1), Some (b, w2) => 
      let w := Nat.max w1 w2 in
      let r := f a b in
      if int_range_ok w r then VInt w r else pg_int_error w
    | _, _ => old (map widen l)
    end
  | _ => old (map widen l)
  end.

Definition pg_int1 (f : Z -> Z) (old : list value -> value) (l : list value) : value :=
  match l with
  | v :: nil =>
    match int_parts v with
    | Some (a, w) => let r := f a in if int_range_ok w r then VInt w r else pg_int_error w
    | None => old (map widen l)
    end
  | _ => old (map widen l)
  end.

(** * Binary floating-point numbers *)

Definition fmt_of (w32 : bool) : format := if w32 then binary32 else binary64.

Definition VF (w32 : bool) (r : fspecial * Qc) : value :=
  Value_F (Some (snd r, (2 * tag_of (fst r) + (if w32 then 1 else 0))%nat)).

(** the float of the format nearest to [q] *)
Definition to_float (w32 : bool) (q : Qc) : value := VF w32 (round_q (fmt_of w32) q).

Definition float_parts (v : value) : option (fspecial * Qc * bool) :=
  match v with
  | Value_F (Some (x, k)) => Some (special_of_tag (Nat.div (Nat.modulo k 10) 2), x, Nat.odd k)
  | _ => None
  end.

Definition is_F (v : value) : bool := match v with Value_F _ => true | _ => false end.

(** the number of decimals of a double of the MySQL family ([Item::decimals]): [None] when it is not fixed
    ([NOT_FIXED_DEC]), the text being then the shortest one; it is kept in [k / 10] ([d + 1], or 0) *)
Definition fdec (v : value) : option nat :=
  match v with Value_F (Some (_, k)) => match Nat.div k 10 with O => None | S d => Some d end | _ => None end.

Definition with_fdec (d : option nat) (v : value) : value :=
  match v with
  | Value_F (Some (x, k)) => Value_F (Some (x, (Nat.modulo k 10 + 10 * match d with Some d => S (Nat.min d 30) | None => O end)%nat))
  | _ => v
  end.
Definition is_F32 (v : value) : bool := match v with Value_F (Some (_, k)) => Nat.odd k | _ => false end.
Definition is_special (v : value) : bool :=
  match float_parts v with Some (F_Finite, _, _) | Some (F_NegZero, _, _) | None => false | _ => true end.

(** the text of a float, as PostgreSQL prints it *)
Definition pg_float_text (v : value) : option string :=
  match float_parts v with
  | Some (sp, x, w) => Some (pg_text (fmt_of w) sp x)
  | None => None
  end.

(** The arithmetic of [float8] and [float4] in PostgreSQL ([float.c]): an operation with a float
    operand converts the other one to a float, and is correctly rounded (the exact result,
    rounded once); [float4] with [float4] gives a [float4], otherwise a [float8]. A result which
    overflows, or a non-zero result which underflows to zero, is an error ([float_overflow_error],
    [float_underflow_error]); division by zero is an error. The infinities and NaN of the operands
    follow IEEE 754. *)
Definition special_op (op : string) (a b : fspecial) (sa sb : bool) : option fspecial :=
  (* [sa], [sb]: the operands are negative (for the infinities and the zeros) *)
  match a, b with
  | F_NaN, _ | _, F_NaN => Some F_NaN
  | F_Finite, F_Finite | F_Finite, F_NegZero | F_NegZero, F_Finite | F_NegZero, F_NegZero => None
  | _, _ =>
    let ia := match a with F_PosInf | F_NegInf => true | _ => false end in
    let ib := match b with F_PosInf | F_NegInf => true | _ => false end in
    match op with
    | "+"%string | "-"%string =>
      let sb' := if String.eqb op "-" then negb sb else sb in
      if ia && ib then (if Bool.eqb sa sb' then Some a else Some F_NaN)
      else if ia then Some a else Some (if sb' then F_NegInf else F_PosInf)
    | "*"%string => Some (if xorb sa sb then F_NegInf else F_PosInf)
    | _ => if ia && ib then Some F_NaN 
           else if ia then Some (if xorb sa sb then F_NegInf else F_PosInf)
           else Some (if xorb sa sb then F_NegZero else F_Finite)
    end
  end.

Definition sign_neg (sp : fspecial) (x : Qc) : bool :=
  match sp with F_NegInf | F_NegZero => true | F_Finite => match Qccompare x (Q2Qc 0) with Lt => true | _ => false end | _ => false end.

Definition float_value (v : value) : option (fspecial * Qc * bool) :=
  match v with
  | Value_F _ => float_parts v
  | Value_Z (Some z) => Some (F_Finite, Qc_of_Z z, false)
  | Value_I (Some (z, _)) => Some (F_Finite, Qc_of_Z z, false)
  | Value_Q (Some q) => Some (F_Finite, q, false)
  | Value_D (Some (q, _, _)) => Some (F_Finite, q, false)
  | _ => None
  end.

Definition pg_flt2 (op : string) (exact : Qc -> Qc -> Qc) (old : list value -> value) (l : list value) : value :=
  match l with
  | v1 :: v2 :: nil =>
    if is_F v1 || is_F v2
    then 
      let w32 := (is_F32 v1 || negb (is_F v1)) && (is_F32 v2 || negb (is_F v2)) in
      match float_value v1, float_value v2 with
      | Some (a, x, _), Some (b, y, _) =>
        match special_op op a b (sign_neg a x) (sign_neg b y) with
        | Some sp => VF w32 (sp, Q2Qc 0)
        | None =>
          if String.eqb op "/" && match Qccompare y (Q2Qc 0) with Eq => true | _ => false end
          then Value_Err "division by zero"
          else
            let r := exact x y in
            let (sp, z) := round_q (fmt_of w32) r in
            match sp with
            | F_PosInf | F_NegInf => Value_Err "value out of range: overflow"
            | _ => if match Qccompare z (Q2Qc 0) with Eq => true | _ => false end &&
                      negb (match Qccompare r (Q2Qc 0) with Eq => true | _ => false end)
                   then Value_Err "value out of range: underflow"
                   else VF w32 (sp, z)
            end
        end
      | _, _ => Value_F None
      end
    else old l
  | _ => old l
  end.

(** [float8] from a text: a number, or ['NaN'], ['Infinity'], ['-Infinity'] ([float8in]) *)
Definition float_of_text (w32 : bool) (t : string) (num : option Qc) : value :=
  let u := string_map lower_ascii t in
  if String.eqb u "nan" then VF w32 (F_NaN, Q2Qc 0)
  else if String.eqb u "infinity" || String.eqb u "inf" then VF w32 (F_PosInf, Q2Qc 0)
  else if String.eqb u "-infinity" || String.eqb u "-inf" then VF w32 (F_NegInf, Q2Qc 0)
  else match num with
       | Some q => let (sp, z) := round_q (fmt_of w32) q in
                   match sp with
                   | F_PosInf | F_NegInf => Value_Err "value out of range"
                   | _ => VF w32 (sp, z)
                   end
       | None => Value_Err "invalid input syntax for type double precision"
       end.

(** * Decimal numbers

    A decimal [Value_D (q, f, s)] has the exact value [q], holds [f] decimal digits, and is
    displayed with [s] decimals. *)

Definition pow10 (n : nat) : Z := Z.pow 10 (Z.of_nat n).
Definition Qc_pow10 (n : nat) : Qc := Qc_of_Z (pow10 n).

(** rounding to [s] decimals, ties away from zero *)
Definition dec_round (q : Qc) (s : nat) : Qc := Qcdiv (Qc_of_Z (Qc_round (Qcmult q (Qc_pow10 s)))) (Qc_pow10 s).

(** truncation to [s] decimals *)
Definition dec_trunc (q : Qc) (s : nat) : Qc := Qcdiv (Qc_of_Z (Qc_trunc (Qcmult q (Qc_pow10 s)))) (Qc_pow10 s).

(** the number of decimals which [q] needs (at most 40) *)
Definition qc_scale (q : Qc) : nat :=
  let d := Zpos (Qden q) in
  match find (fun s => Z.eqb (Z.modulo (pow10 s) d) 0) (seq 0 41) with
  | Some s => s
  | None => 40%nat
  end.

(** the text of [q] with exactly [s] decimals (rounded) *)
Definition dec_text (q : Qc) (s : nat) : string :=
  let z := Qc_round (Qcmult q (Qc_pow10 s)) in
  let m := pow10 s in
  let fp := string_of_Z (Z.abs z mod m) in
  (if Z.ltb z 0 then "-" else "") ++ string_of_Z (Z.abs z / m) ++
  (if Nat.eqb s 0 then "" else "." ++ string_repeat (s - String.length fp) "0" ++ fp).

Definition VDec (q : Qc) (f s : nat) : value := Value_D (Some (q, f, s)).

Definition is_D (v : value) : bool := match v with Value_D _ => true | _ => false end.

(** the value, the digits held and the scale of a number, an integer having scale 0 *)
Definition dec_of_value (v : value) : option (Qc * nat * nat) :=
  match v with
  | Value_D d => d
  | Value_Z (Some z) => Some (Qc_of_Z z, 0%nat, 0%nat)
  | Value_I (Some (z, _)) => Some (Qc_of_Z z, 0%nat, 0%nat)
  | Value_Q (Some q) => Some (q, qc_scale q, qc_scale q)
  | _ => None
  end.

(** a decimal literal: [VD 150 2] is [1.50] *)
Definition dec_lit (n : Z) (s : nat) : value := VDec (Qcdiv (Qc_of_Z n) (Qc_pow10 s)) s s.

(** ** The scale of a quotient in PostgreSQL ([select_div_scale], [src/backend/utils/adt/numeric.c])

    The digits of a [numeric] are in base [NBASE] = 10000 ([DEC_DIGITS] = 4). The weight of a
    non-zero number is the position of its first non-zero base-10000 digit; the scale of the
    quotient gives at least [NUMERIC_MIN_SIG_DIGITS] = 16 significant digits, and is not below the
    scales of the operands. *)
Fixpoint weight_up (fuel : nat) (n d : Z) (w : Z) : Z :=
  match fuel with
  | O => w
  | S f => if Z.leb (Z.mul d (Z.pow 10000 (w + 1))) n then weight_up f n d (w + 1) else w
  end.

Fixpoint weight_down (fuel : nat) (n d : Z) (k : Z) : Z :=
  match fuel with
  | O => k
  | S f => if Z.leb d (Z.mul n (Z.pow 10000 k)) then k else weight_down f n d (k + 1)
  end.

(** the weight and the first base-10000 digit of [q] (0 and 0 for zero) *)
Definition nbase_weight (q : Qc) : Z * Z :=
  let n := Z.abs (Qnum q) in
  let d := Zpos (Qden q) in
  if Z.eqb n 0 then (0%Z, 0%Z)
  else if Z.leb d n 
       then let w := weight_up 300 n d 0 in (w, Z.div n (Z.mul d (Z.pow 10000 w)))
       else let k := weight_down 300 n d 1 in (Z.opp k, Z.div (Z.mul n (Z.pow 10000 k)) d).

Definition pg_div_scale (q1 : Qc) (s1 : nat) (q2 : Qc) (s2 : nat) : nat :=
  let (w1, f1) := nbase_weight q1 in
  let (w2, f2) := nbase_weight q2 in
  let qw := if Z.leb f1 f2 then (w1 - w2 - 1)%Z else (w1 - w2)%Z in
  let r := Z.max (16 - qw * 4) (Z.max (Z.of_nat s1) (Z.of_nat s2)) in
  Z.to_nat (Z.min (Z.max r 0) 1000).

(** ** The arithmetic of [numeric] in PostgreSQL: [+] and [-] have the larger scale, [*] the sum
    of the scales ([mul_var] with [rscale = dscale1 + dscale2]), [/] the scale of
    [select_div_scale], rounded ties away from zero ([round_var]). An integer operand has scale 0;
    two integers keep the integer arithmetic. *)
Definition pg_dec2 (op : Qc * nat -> Qc * nat -> value) (old : list value -> value) (l : list value) : value :=
  match l with
  | v1 :: v2 :: nil =>
    if (is_D v1 || is_D v2) && negb (is_F v1 || is_F v2)
    then match dec_of_value v1, dec_of_value v2 with
         | Some (q1, _, s1), Some (q2, _, s2) => op (q1, s1) (q2, s2)
         | _, _ => Value_D None
         end
    else old l
  | _ => old l
  end.

Definition pg_dec_plus (a b : Qc * nat) := VDec (Qcplus (fst a) (fst b)) (Nat.max (snd a) (snd b)) (Nat.max (snd a) (snd b)).
Definition pg_dec_minus (a b : Qc * nat) := VDec (Qcminus (fst a) (fst b)) (Nat.max (snd a) (snd b)) (Nat.max (snd a) (snd b)).
Definition pg_dec_mult (a b : Qc * nat) := VDec (Qcmult (fst a) (fst b)) (snd a + snd b) (snd a + snd b).
(** [numeric_mod]: [x - trunc (x / y) * y], with the larger scale; a zero divisor is an error *)
Definition pg_dec_mod (a b : Qc * nat) :=
  if Qc_is_zero (fst b) then Value_Err "division by zero"
  else VDec (Qcminus (fst a) (Qcmult (Qc_of_Z (Qc_trunc (Qcdiv (fst a) (fst b)))) (fst b)))
            (Nat.max (snd a) (snd b)) (Nat.max (snd a) (snd b)).
Definition pg_dec_div (a b : Qc * nat) := 
  let r := pg_div_scale (fst a) (snd a) (fst b) (snd b) in
  VDec (dec_round (Qcdiv (fst a) (fst b)) r) r r.

(** * JSON ([Json.v])

    A [Value_J] holds the compact text of a JSON value; a normalized value (MySQL [JSON], PostgreSQL [jsonb])
    has its objects sorted and without duplicated keys. *)
Definition VJ (k : nat) (j : json) : value :=
  Value_J (Some (text_compact (if Nat.eqb k 0 then normalize j else j), k)).

Definition json_of_J (v : value) : option json :=
  match v with Value_J (Some (t, _)) => parse_json t | _ => None end.

(** PostgreSQL [to_jsonb]: a number, a string, a boolean, [null]; a date is its text *)
Definition pg_json_of_value (v : value) : json :=
  if is_null v then JNull else
  match v with
  | Value_Z (Some z) | Value_I (Some (z, _)) => JNum (string_of_Z z)
  | Value_D (Some (q, _, sc)) => JNum (dec_text q sc)
  | Value_Q (Some q) => JNum (dec_text q (qc_scale q))
  | Value_F _ => match pg_float_text v with Some t => JNum t | None => JNull end
  | Value_string (Some t) | Value_C (Some (t, _)) => JStr t
  | Value_bool (Some b) => JBool b
  | Value_J _ => match json_of_J v with Some j => j | None => JNull end
  | _ => match pg_temporal_text v with Some t => JStr t | None => JNull end
  end.

(** the text of an array: [{1,2,NULL}], an element being quoted when it is empty, [NULL], or holds a space,
    a brace, a comma, a double quote or a backslash ([array_out]) *)
Definition backslash : ascii := ascii_of_nat 92.
Definition dquote : ascii := ascii_of_nat 34.

Definition array_elem_text (j : json) : string :=
  match j with
  | JNull => "NULL"
  | JNum t => t
  | JBool b => if b then "t" else "f"
  | JStr t =>
    let special := existsb (fun c => Ascii.eqb c " "%char || Ascii.eqb c "{"%char || Ascii.eqb c "}"%char
                                     || Ascii.eqb c ","%char || Ascii.eqb c dquote || Ascii.eqb c backslash)
                           (list_ascii_of_string t)
                   || String.eqb t "" || String.eqb (string_map upper_ascii t) "NULL" in
    if special
    then String dquote (string_of_list_ascii (flat_map (fun c => if Ascii.eqb c dquote || Ascii.eqb c backslash
                                                                then backslash :: c :: nil else c :: nil)
                                                      (list_ascii_of_string t)) ++ String dquote EmptyString)
    else t
  | _ => text_compact j
  end.

Definition array_text (t : string) : string :=
  match parse_json t with
  | Some (JArr l) => "{" ++ String.concat "," (map array_elem_text l) ++ "}"
  | _ => t
  end.

Definition pg_json_text (v : value) : option string :=
  match v with
  | Value_J (Some (t, 2%nat)) => Some (array_text t)
  | Value_J (Some (t, 1%nat)) => Some t
  | Value_J (Some (t, _)) => match parse_json t with Some j => Some (text_spaced j) | None => Some t end
  | _ => None
  end.

Definition json_kind (v : value) : nat := match v with Value_J (Some (_, k)) => k | _ => 0%nat end.

(** [j -> k]: the member [k] of an object, or the element [k] of an array (from the end if negative) *)
Definition pg_json_get (as_text : bool) (j k : value) : value :=
  match json_of_J j with
  | Some d =>
    let st := match k with
              | Value_string (Some key) => Some (SKey key)
              | Value_Z (Some i) | Value_I (Some (i, _)) => Some (SIdx i)
              | _ => None end in
    match st with
    | Some st => match follow (st :: nil) d with
                 | Some r => if as_text 
                             then match r with JStr t => Value_string (Some t) | JNull => Value_string None 
                                             | _ => Value_string (Some (text_spaced r)) end
                             else VJ (json_kind j) r
                 | None => if as_text then Value_string None else Value_J None end
    | None => if as_text then Value_string None else Value_J None
    end
  | None => if as_text then Value_string None else Value_J None
  end.

(** [j #> '{a,0}']: a path given as a text array *)
Definition pg_path_of_text (t : string) : list step :=
  let inner := match t with String "{" r => substring 0 (String.length r - 1) r | _ => t end in
  map (fun w => match Z_of_string w with Some i => SIdx i | None => SKey w end)
      (filter (fun w => negb (String.eqb w EmptyString)) (split_at "," inner)).

Definition pg_json_path (as_text : bool) (j p : value) : value :=
  match json_of_J j, p with
  | Some d, Value_string (Some t) =>
    match follow (pg_path_of_text t) d with
    | Some r => if as_text then match r with JStr x => Value_string (Some x) | JNull => Value_string None 
                                         | _ => Value_string (Some (text_spaced r)) end
                else VJ (json_kind j) r
    | None => if as_text then Value_string None else Value_J None
    end
  | _, _ => if as_text then Value_string None else Value_J None
  end.

Definition pg_json_typeof (j : json) : string :=
  match j with JNull => "null" | JBool _ => "boolean" | JNum _ => "number" | JStr _ => "string" | JArr _ => "array" | JObj _ => "object" end.

Fixpoint pairs_of (l : list value) : option (list (string * json)) :=
  match l with
  | nil => Some nil
  | k :: v :: r => match k, pairs_of r with
                   | Value_string (Some key), Some rest => Some ((key, pg_json_of_value v) :: rest)
                   | Value_Z (Some z), Some rest => Some ((string_of_Z z, pg_json_of_value v) :: rest)
                   | _, _ => None end
  | _ => None
  end.

(** * Casts (PostgreSQL). A string which is not the text of a value of the target type is an
    error ([invalid input syntax for type ...], [src/backend/utils/adt/int.c], [numeric.c],
    [bool.c]). *)

(** [float8] to an integer: [rint], ties to even ([dtoi4]); NaN and the infinities are out of range *)
Definition float_to_Z (v : value) : value :=
  match float_parts v with
  | Some (F_Finite, x, _) | Some (F_NegZero, x, _) =>
    Value_Z (Some (if Z.ltb (Qnum x) 0 then Z.opp (round_half_even (Z.opp (Qnum x)) (Zpos (Qden x)))
                   else round_half_even (Qnum x) (Zpos (Qden x))))
  | Some _ => Value_Err "integer out of range"
  | None => Value_Z None
  end.

(** [float8] to [numeric]: the text with [DBL_DIG] = 15 significant digits ([float8_numeric]),
    [float4]: [FLT_DIG] = 6 *)
Definition float_to_numeric (v : value) : value :=
  match float_parts v with
  | Some (F_Finite, x, w) =>
    if match Qccompare x (Q2Qc 0) with Eq => true | _ => false end then VDec x 0 0
    else
      let n := Z.abs (Qnum x) in
      let d := Zpos (Qden x) in
      let (dd0, e0) := digits_round n d (if w then 6 else 15) in
      let (dd, e) := strip_zeros dd0 e0 in
      let q := Q2Qc (q_of_digits (if Z.ltb (Qnum x) 0 then Z.opp dd else dd) e) in
      let sc := Z.to_nat (Z.max 0 (Z.opp e)) in
      VDec q sc sc
  | Some (F_NegZero, _, _) => VDec (Q2Qc 0) 0 0
  | Some (F_NaN, _, _) => Value_Err "cannot convert NaN to numeric"
  | Some _ => Value_Err "cannot convert infinity to numeric"
  | None => Value_D None
  end.

Definition cast_float (w32 : bool) (v : value) : value :=
  match v with
  | Value_F (Some (x, k)) => if w32 then VF true (round_q binary32 x) else Value_F (Some (x, (2 * Nat.div (Nat.modulo k 10) 2)%nat))
  | Value_Z (Some z) => to_float w32 (Qc_of_Z z)
  | Value_Q (Some q) => to_float w32 q
  | Value_D (Some (q, _, _)) => to_float w32 q
  | Value_string (Some t) => 
    let t := string_rtrim (string_ltrim t) in float_of_text w32 t (Qc_of_string t)
  | _ => Value_F None
  end.

Definition cast_Z v :=
  match v with
  | Value_F _ => float_to_Z v
  | Value_Z z => Value_Z z
  | Value_Q (Some q) => Value_Z (Some (Qc_round q))
  (* a [numeric] is rounded ([numeric_int4]: half away from zero), then checked against the range *)
  | Value_D (Some (q, _, _)) => Value_Z (Some (Qc_round q))
  | Value_string (Some s) => 
    match Z_of_string (string_rtrim (string_ltrim s)) with
    | Some z => Value_Z (Some z)
    | None => Value_Err "invalid input syntax for type integer"
    end
  | Value_bool (Some b) => Value_Z (Some (if b then 1%Z else 0%Z))
  | _ => Value_Z None
  end.

Definition cast_Q v :=
  match v with
  | Value_F _ => float_to_numeric v
  | Value_Q q => Value_Q q
  | Value_Z (Some z) => Value_Q (Some (Qc_of_Z z))
  | Value_D d => Value_D d
  | Value_string (Some s) => 
    let t := string_rtrim (string_ltrim s) in
    match Qc_of_string t with
    | Some q => 
      let sc := match String.index 0 "." t with Some i => (String.length t - S i)%nat | None => 0%nat end in
      VDec q sc sc
    | None => Value_Err "invalid input syntax for type numeric"
    end
  | _ => Value_Q None
  end.

Definition cast_string v :=
  Value_string
    match v with
    | Value_string s => s
    | Value_Z (Some z) => Some (string_of_Z z)
    | Value_I (Some (z, _)) => Some (string_of_Z z)
    | Value_Q (Some q) => Some (string_of_Qc q)
    | Value_D (Some (q, _, sc)) => Some (dec_text q sc)
    | Value_F _ => pg_float_text v
    | Value_T _ | Value_V _ => pg_temporal_text v
    | Value_J _ => pg_json_text v
    | Value_bool (Some b) => Some (if b then "true" else "false")
    | _ => None
    end.

Definition cast_bool v :=
  match v with
  | Value_bool b => Value_bool b
  | Value_Z (Some z) => Value_bool (Some (negb (Z.eqb z 0)))
  | Value_string (Some s) => 
    match bool_of_string (string_rtrim (string_ltrim s)) with
    | Some b => Value_bool (Some b)
    | None => Value_Err "invalid input syntax for type boolean"
    end
  | _ => Value_bool None
  end.

(** * Interpretation of predicates

    All the comparison predicates follow the three-valued logic of SQL: they are
    UNKNOWN as soon as one of their arguments is NULL. The IS predicates are
    two-valued. *)

Definition between3 (l : list value) :=
  match l with
  | x :: lo :: hi :: nil => andb3 (sql_le3 lo x) (sql_le3 x hi)
  | _ => unknown3
  end.

Definition predicate_table : list (string * (list value -> bool3)) :=
     (* [jsonb @> jsonb], [<@], [jsonb ? key] *)
     ("@>", binary3 (fun a b => match json_of_J a, json_of_J b with 
                                | Some x, Some y => bool3_of_bool (json_contains (json_size x + json_size y) x y) | _, _ => unknown3 end))
  :: ("<@", binary3 (fun a b => match json_of_J a, json_of_J b with 
                                | Some x, Some y => bool3_of_bool (json_contains (json_size x + json_size y) y x) | _, _ => unknown3 end))
  :: ("?", binary3 (fun a k => match json_of_J a, k with
                               | Some (JObj l), Value_string (Some key) => bool3_of_bool (existsb (fun m => String.eqb (fst m) key) l)
                               | Some (JArr l), Value_string (Some key) => bool3_of_bool (existsb (fun x => match x with JStr t => String.eqb t key | _ => false end) l)
                               | Some _, Value_string (Some _) => false3
                               | _, _ => unknown3 end))
  :: ("=", binary3 sql_eq3)
  :: ("<>", binary3 (fun a b => negb3 (sql_eq3 a b)))
  :: ("!=", binary3 (fun a b => negb3 (sql_eq3 a b)))
  :: ("<", binary3 sql_lt3)
  :: ("<=", binary3 sql_le3)
  :: (">", binary3 (fun a b => sql_lt3 b a))
  :: (">=", binary3 (fun a b => sql_le3 b a))
  :: ("is null", unary3 (fun v => bool3_of_bool (is_null v)))
  :: ("is not null", unary3 (fun v => bool3_of_bool (negb (is_null v))))
  :: ("is true", unary3 (fun v => bool3_of_bool (value_eqb v (Value_bool (Some true)))))
  :: ("is not true", unary3 (fun v => bool3_of_bool (negb (value_eqb v (Value_bool (Some true))))))
  :: ("is false", unary3 (fun v => bool3_of_bool (value_eqb v (Value_bool (Some false)))))
  :: ("is not false", unary3 (fun v => bool3_of_bool (negb (value_eqb v (Value_bool (Some false))))))
  :: ("is unknown", unary3 (fun v => bool3_of_bool (value_eqb v (Value_bool None))))
  :: ("is not unknown", unary3 (fun v => bool3_of_bool (negb (value_eqb v (Value_bool None)))))
  :: ("is distinct from", binary3 (fun a b => bool3_of_bool (negb (not_distinct a b))))
  :: ("is not distinct from", binary3 (fun a b => bool3_of_bool (not_distinct a b)))
  :: ("between", between3)
  :: ("not between", fun l => negb3 (between3 l))
  :: ("like", binary3 like3)
  :: ("not like", binary3 (fun a b => negb3 (like3 a b)))
  :: ("in", in_list3)
  :: ("not in", fun l => negb3 (in_list3 l))
  :: ("row=", fun l => let (l1, l2) := split_half l in row_eq3 l1 l2)
  :: ("row<>", fun l => let (l1, l2) := split_half l in negb3 (row_eq3 l1 l2))
  :: ("true", fun _ => true3)
  :: ("false", fun _ => false3)
  :: ("unknown", fun _ => unknown3)
  :: nil.

Fixpoint string_assoc (A : Type) (s : string) (l : list (string * A)) : option A :=
  match l with
  | nil => None
  | (s', a) :: l => if String.eqb s s' then Some a else string_assoc A s l
  end.

(** A predicate which is not in the table is UNKNOWN. *)
Definition interp_predicate p : list value -> bool3 :=
  match p with
  | Predicate s =>
    match string_assoc _ s predicate_table with
    | Some f => fun l => f (map widen l)
    | None => fun _ => unknown3
    end
  end.

(** * Interpretation of function symbols *)

Definition strict_string1 (f : string -> value) (l : list value) :=
  match l with
  | Value_string (Some s) :: nil => f s
  | _ => Value_string None
  end.

Definition string_fun1 (f : string -> string) :=
  strict_string1 (fun s => Value_string (Some (f s))).

Fixpoint coalesce (l : list value) :=
  match l with
  | nil => Value_Z None
  | v :: nil => v
  | v :: l => if is_null v then coalesce l else v
  end.

(** CASE WHEN c1 THEN v1 ... WHEN cn THEN vn [ELSE e] END, the arguments being
    [c1 :: v1 :: ... :: cn :: vn :: nil] or [c1 :: v1 :: ... :: cn :: vn :: e :: nil].
    Without ELSE branch, the result is the NULL of the type of the first branch. *)
Fixpoint case_when (d : value) (l : list value) :=
  match l with
  | nil => d
  | e :: nil => e
  | c :: v :: l => match bool3_of_value c with true3 => v | _ => case_when d l end
  end.

Definition sql_case (l : list value) :=
  match l with
  | _ :: v :: _ => case_when (default_value (type_of_value v)) l
  | _ => case_when (Value_Z None) l
  end.

(** GREATEST / LEAST ignore NULLs (PostgreSQL); they are NULL only when all
    their arguments are. *)
Definition pick (keep : comparison -> bool) (a b : value) :=
  if is_null a then b
  else if is_null b then a
       else if keep (sql_order a b) then a else b.

Definition extremum (keep : comparison -> bool) (l : list value) :=
  match l with
  | nil => Value_Z None
  | v :: l => fold_left (pick keep) l v
  end.

Definition concat_ws (l : list value) :=
  (* CONCAT ignores NULLs *)
  Value_string
    (Some (fold_left
             (fun acc v => match cast_string v with
                           | Value_string (Some s) => acc ++ s
                           | _ => acc
                           end) l EmptyString)).

(** * Dates and times in PostgreSQL ([date.c], [timestamp.c])

    [date + integer] and [date - integer] are dates, [date - date] is an [integer] number of days,
    [date + interval] and [timestamp +/- interval] are timestamps (months first, the day clamped to the
    end of the month, then days, then microseconds), [timestamp - timestamp] is an interval of days
    and microseconds ([interval_justify_hours]), [date + time] is a timestamp. *)
Definition int_of (v : value) : option Z :=
  match v with Value_Z (Some z) | Value_I (Some (z, _)) => Some z | _ => None end.

Definition neg_interval (iv : Z * Z * Z) : Z * Z * Z := let '(a, b, c) := iv in (- a, - b, - c).

Definition pg_tm2 (minus : bool) (old : list value -> value) (l : list value) : value :=
  match l with
  | v1 :: v2 :: nil =>
    match v1, v2 with
    | Value_T (Some _), _ | _, Value_T (Some _) | Value_V (Some _), _ | _, Value_V (Some _) =>
      match temporal_parts v1, temporal_parts v2, v1, v2 with
      (* date +/- integer *)
      | Some (0%nat, d, _), None, _, _ => 
        match int_of v2 with Some n => VDate (if minus then d - n else d + n) | None => 
        match v2 with 
        | Value_V (Some iv) => VTs (ts_plus_interval (ts_of d 0) (if minus then neg_interval iv else iv)) 6
        | _ => Value_Err "operator does not exist" end end
      | None, Some (0%nat, d, _), _, _ => 
        match int_of v1, minus with Some n, false => VDate (d + n) | _, _ => 
        match v1, minus with 
        | Value_V (Some iv), false => VTs (ts_plus_interval (ts_of d 0) iv) 6
        | _, _ => Value_Err "operator does not exist" end end
      | Some (0%nat, a, _), Some (0%nat, b, _), _, _ => 
        if minus then VInt 32 (a - b) else Value_Err "operator does not exist"
      | Some (0%nat, d, _), Some (1%nat, u, f), _, _ => if minus then Value_Err "operator does not exist" else VTs (ts_of d u) f
      | Some (k, t, f), None, _, Value_V (Some iv) => 
        if Nat.eqb k 1 then VTime (Z.modulo (t + (if minus then - snd iv else snd iv)) usec_per_day) f
        else Value_T (Some (ts_plus_interval t (if minus then neg_interval iv else iv), (k + 10 * f)%nat))
      | None, Some (k, t, f), Value_V (Some iv), _ => 
        if minus || Nat.eqb k 1 then Value_Err "operator does not exist"
        else Value_T (Some (ts_plus_interval t iv, (k + 10 * f)%nat))
      | Some (_, _, _), Some (_, _, _), _, _ =>
        if minus 
        then match to_ts v1, to_ts v2 with
             | Some a, Some b => let dlt := a - b in VIntv 0 (Z.quot dlt usec_per_day) (Z.rem dlt usec_per_day)
             | _, _ => match temporal_parts v1, temporal_parts v2 with
                       | Some (1%nat, a, _), Some (1%nat, b, _) => VIntv 0 0 (a - b)
                       | _, _ => Value_Err "operator does not exist" end
             end
        else Value_Err "operator does not exist"
      | None, None, Value_V (Some (a1, b1, c1)), Value_V (Some (a2, b2, c2)) =>
        if minus then VIntv (a1 - a2) (b1 - b2) (c1 - c2) else VIntv (a1 + a2) (b1 + b2) (c1 + c2)
      | _, _, _, _ => Value_Err "operator does not exist"
      end
    | _, _ => old l
    end
  | _ => old l
  end.

(** [EXTRACT(field FROM v)]: a [numeric] (PostgreSQL 14), with 6 decimals for the seconds and the epoch
    of a timestamp; [date_part] is the same number as a [float8] *)
Definition pg_extract (field : string) (v : value) : value :=
  let f := string_map lower_ascii field in
  let num (z : Z) := VDec (Qc_of_Z z) 0 0 in
  let micro (us : Z) := VDec (Qcdiv (Qc_of_Z us) (Qc_of_Z 1000000)) 6 6 in
  match v with
  | Value_V (Some (mo, d, us)) =>
    match f with
    | "year" => num (Z.quot mo 12) | "month" => num (Z.rem mo 12) | "day" => num d
    | "hour" => num (Z.quot us 3600000000) | "minute" => num (Z.rem (Z.quot us 60000000) 60)
    | "second" => micro (Z.rem us 60000000)
    | "epoch" => micro (interval_usec (mo, d, us) + Z.quot mo 12 * 5 * usec_per_day / 4)
    | _ => Value_Err "unit not supported" end
  | _ =>
  match temporal_parts v with
  | Some (k, n, _) =>
    let '(days, us) := match k with
                       | 0%nat => (n, 0)
                       | 1%nat => (0, n)
                       | _ => (ts_days n, ts_usec n) end in
    let '(y, m, d) := civil_from_days days in
    match f with
    | "year" => num y | "month" => num m | "day" => num d
    | "quarter" => num ((m - 1) / 3 + 1)
    | "decade" => num (Z.div y 10) | "century" => num (if Z.leb y 0 then (y - 100) / 100 else (y + 99) / 100)
    | "millennium" => num (if Z.leb y 0 then (y - 1000) / 1000 else (y + 999) / 1000)
    | "dow" => num (day_of_week days) | "isodow" => num (iso_weekday days) | "doy" => num (day_of_year days)
    | "week" => num (snd (iso_week_year days)) | "isoyear" => num (fst (iso_week_year days))
    | "hour" => num (us / 3600000000) | "minute" => num ((us / 60000000) mod 60)
    | "second" => micro (us mod 60000000)
    | "milliseconds" => VDec (Qcdiv (Qc_of_Z (us mod 60000000)) (Qc_of_Z 1000)) 3 3
    | "microseconds" => num (us mod 60000000)
    | "epoch" => match k with 0%nat => num (days * 86400) | 1%nat => micro n | _ => micro n end
    | _ => Value_Err "unit not recognized"
    end
  | None => if is_null v then Value_D None else Value_Err "function does not exist"
  end
  end%string.

(** [date_trunc(field, v)]: a timestamp *)
Definition pg_date_trunc (field : string) (v : value) : value :=
  let f := string_map lower_ascii field in
  match to_ts v, temporal_parts v with
  | Some t, Some (k, _, fsp) =>
    let days := ts_days t in
    let us := ts_usec t in
    let '(y, m, _) := civil_from_days days in
    let r := match f with
             | "millennium" => Some (ts_of (days_from_civil ((y - 1) / 1000 * 1000 + 1) 1 1) 0)
             | "century" => Some (ts_of (days_from_civil ((y - 1) / 100 * 100 + 1) 1 1) 0)
             | "decade" => Some (ts_of (days_from_civil (y / 10 * 10) 1 1) 0)
             | "year" => Some (ts_of (days_from_civil y 1 1) 0)
             | "quarter" => Some (ts_of (days_from_civil y ((m - 1) / 3 * 3 + 1) 1) 0)
             | "month" => Some (ts_of (days_from_civil y m 1) 0)
             | "week" => Some (ts_of (days - iso_weekday days + 1) 0)
             | "day" => Some (ts_of days 0)
             | "hour" => Some (ts_of days (us / 3600000000 * 3600000000))
             | "minute" => Some (ts_of days (us / 60000000 * 60000000))
             | "second" => Some (ts_of days (us / 1000000 * 1000000))
             | "milliseconds" => Some (ts_of days (us / 1000 * 1000))
             | "microseconds" => Some t
             | _ => None
             end%string in
    match r with
    | Some r => Value_T (Some (r, ((if Nat.eqb k 0 then 3 else k) + 10 * fsp)%nat))
    | None => Value_Err "unit not recognized"
    end
  | _, _ => if is_null v then Value_T None else Value_Err "function does not exist"
  end.

(** [interval] from a text: [n unit [n unit ...]] and an optional [HH:MM:SS] ([interval_in], postgres style) *)
Fixpoint parse_interval_words (fuel : nat) (ws : list string) : option (Z * Z * Z) :=
  match fuel with
  | O => None
  | S f =>
    match ws with
    | nil => Some (0, 0, 0)
    | w :: nil => match parse_time w with Some u => Some (0, 0, u) | None => None end
    | n :: u :: r =>
      match Z_of_string n, interval_of_unit 1 u with
      | Some n, Some (a, b, c) => 
        match parse_interval_words f r with Some (a', b', c') => Some (n * a + a', n * b + b', n * c + c') | None => None end
      | _, _ => match parse_time n with
                | Some us => match parse_interval_words f (u :: r) with Some (a', b', c') => Some (a', b', us + c') | None => None end
                | None => None end
      end
    end
  end.

Definition cast_interval (v : value) : value :=
  match v with
  | Value_V _ => v
  | Value_string (Some t) => 
    match parse_interval_words 20 (filter (fun w => negb (String.eqb w EmptyString)) (split_at " " (string_rtrim (string_ltrim t)))) with
    | Some (a, b, c) => VIntv a b c
    | None => Value_Err "invalid input syntax for type interval"
    end
  | _ => if is_null v then Value_V None else Value_Err "cannot cast to interval"
  end.

Definition pg_cast_temporal (kind : nat) (v : value) : value :=
  match v with
  | Value_string (Some t) =>
    let t := string_rtrim (string_ltrim t) in
    match kind with
    | 0%nat => match parse_date t with Some d => VDate d | None => 
               match parse_timestamp t with Some x => VDate (ts_days x) | None => Value_Err "invalid input syntax for type date" end end
    | 1%nat => match parse_time t with Some u => VTime u 6 | None => Value_Err "invalid input syntax for type time" end
    | _ => match parse_timestamp t with Some u => Value_T (Some (u, (kind + 60)%nat)) | None => Value_Err "invalid input syntax for type timestamp" end
    end
  | Value_T (Some _) =>
    match kind, to_ts v, temporal_parts v with
    | 0%nat, Some x, _ => VDate (ts_days x)
    | 1%nat, Some x, _ => VTime (ts_usec x) 6
    | 1%nat, None, Some (1%nat, u, f) => VTime u f
    | _, Some x, _ => Value_T (Some (x, (kind + 60)%nat))
    | _, _, _ => Value_Err "cannot cast"
    end
  | _ => if is_null v then Value_T None else Value_Err "cannot cast"
  end.

(** * Mathematical functions

    The functions of the C library are correctly rounded ([IEEE.v]). [math_arg] is the argument of a
    function of doubles: a float with its special value, or a number. *)
Definition math_arg (conv : value -> option num) (v : value) : option (fspecial * Q) :=
  match v with
  | Value_F (Some (x, k)) =>
    match special_of_tag (Nat.div (Nat.modulo k 10) 2) with
    | F_NegZero => Some (F_Finite, 0%Q)
    | sp => Some (sp, this x)
    end
  | _ => match conv v with
         | Some (Num_Z z) => Some (F_Finite, inject_Z z)
         | Some (Num_Q q) => Some (F_Finite, this q)
         | None => None
         end
  end.

(** a function of one double: [f] on a finite argument ([None] outside its domain, where the value is
    [dom]), [sp] on an infinite or NaN one; [bad] is the value of an argument which is not a number *)
Definition dbl_fun1 (conv : value -> option num) (f : Q -> option (fspecial * Qc)) (dom : value)
           (sp : fspecial -> value) (bad : value) (l : list value) : value :=
  match l with
  | v :: nil =>
    if is_null v then Value_F None
    else match math_arg conv v with
         | Some (F_Finite, q) => match f q with Some r => VF false r | None => dom end
         | Some (s, _) => sp s
         | None => bad
         end
  | _ => Value_Err "function does not exist"
  end.

Definition dbl_fun2 (conv : value -> option num) (f : Q -> Q -> option (fspecial * Qc)) (dom : value)
           (bad : value) (l : list value) : value :=
  match l with
  | a :: b :: nil =>
    if is_null a || is_null b then Value_F None
    else match math_arg conv a, math_arg conv b with
         | Some (F_Finite, x), Some (F_Finite, y) => match f x y with Some r => VF false r | None => dom end
         | Some (F_NaN, _), _ | _, Some (F_NaN, _) => VF false (F_NaN, Qc_of_Z 0)
         | Some _, Some _ => dom
         | _, _ => bad
         end
  | _ => Value_Err "function does not exist"
  end.

Definition pi_q : Q := this pi_double.

(** [degrees] and [radians] as C computes them: [x * 180.0 / M_PI] and [x * M_PI / 180.0] (two roundings,
    SQLite), or with the constant [180 / M_PI] rounded first (MySQL), or dividing by the double
    [RADIANS_PER_DEGREE] (PostgreSQL) *)
Definition r64 (q : Q) : Q := this (snd (round_q binary64 q)).
Definition degrees_c (x : Q) : fspecial * Qc := round_q binary64 (Qdiv (r64 (Qmult x 180)) pi_q).
Definition radians_c (x : Q) : fspecial * Qc := round_q binary64 (Qdiv (r64 (Qmult x pi_q)) 180).
Definition degrees_my (x : Q) : fspecial * Qc := round_q binary64 (Qmult x (r64 (Qdiv 180 pi_q))).
Definition radians_my (x : Q) : fspecial * Qc := round_q binary64 (Qmult x (r64 (Qdiv pi_q 180))).
Definition pg_rad_per_deg : Q := r64 (Qdiv pi_q 180).
Definition degrees_pg (x : Q) : fspecial * Qc := round_q binary64 (Qdiv x pg_rad_per_deg).
Definition radians_pg (x : Q) : fspecial * Qc := round_q binary64 (Qmult x pg_rad_per_deg).

(** [x ^ y] of the C library: an integer exponent is exact before the rounding; a negative base with a
    non-integer exponent, and zero with a negative exponent, are outside the domain *)
Definition pow_c (x y : Q) : option (fspecial * Qc) :=
  let yc := Qred y in
  if Z.eqb (Zpos (Qden yc)) 1 then
    let n := Qnum yc in
    if Z.eqb (Qnum x) 0 then (if Z.ltb n 0 then None else Some (round_q binary64 (if Z.eqb n 0 then 1%Q else 0%Q)))
    else if Z.ltb (Z.abs n) 100000 then Some (round_q binary64 (Qpower x n))
    else pow_q binary64 x y
  else if Z.ltb (Qnum x) 0 then None
  else if Z.eqb (Qnum x) 0 then Some (F_Finite, Qc_of_Z 0)
  else pow_q binary64 x y.

(** [log (b, x)] of doubles *)
Definition log2_c (b x : Q) : option (fspecial * Qc) :=
  if Z.leb (Qnum b) 0 || Z.leb (Qnum x) 0 || Qeq_bool b 1 then None
  else Some (round_q binary64 (Qdiv (ln_exact x) (ln_exact b))).

(** ** The functions of [numeric] in PostgreSQL ([numeric_sqrt], [numeric_exp], [numeric_ln], [log_var]):
    the scale gives at least [NUMERIC_MIN_SIG_DIGITS] = 16 significant digits and is not below the
    scale of the argument; the result is rounded ties away from zero. *)
Definition Qc_lt_bool (a b : Qc) : bool := match Qccompare a b with Lt => true | _ => false end.
Definition Qc_le_bool (a b : Qc) : bool := match Qccompare a b with Gt => false | _ => true end.
Definition Qc_eq_bool (a b : Qc) : bool := match Qccompare a b with Eq => true | _ => false end.

(** [power] of [double precision] ([dpow] of [float.c]): [NaN ^ 0] and [1 ^ NaN] are 1, the other powers of or by a
    NaN are NaN; zero to a negative power and a negative number to a non-integer power are errors; an infinite
    exponent gives 1 for [|x| = 1], an infinity or 0 by the side of [|x|] around 1; a power of an infinity is 1
    for the exponent 0, an infinity or 0 by the sign of the exponent, and for [-Infinity] the sign of the result
    is that of an odd exponent. *)
Definition pg_dpow (conv : value -> option num) (dom bad : value) (l : list value) : value :=
  match l with
  | a :: b :: nil =>
    if is_null a || is_null b then Value_F None
    else match math_arg conv a, math_arg conv b with
         | Some (sa, x), Some (sb, y) =>
           let one := VF false (F_Finite, Qc_of_Z 1) in
           let zero := VF false (F_Finite, Qc_of_Z 0) in
           let nan := VF false (F_NaN, Qc_of_Z 0) in
           let pinf := VF false (F_PosInf, Qc_of_Z 0) in
           let fin (s : fspecial) := match s with F_Finite | F_NegZero => true | _ => false end in
           let neg (s : fspecial) (q : Q) := match s with F_NegInf => true | F_PosInf | F_NaN => false | _ => Z.ltb (Qnum q) 0 end in
           let is0 (s : fspecial) (q : Q) := fin s && Z.eqb (Qnum q) 0 in
           let yred := Qred y in
           let yint := fin sb && Pos.eqb (Qden yred) 1 in
           match sa, sb with
           | F_NaN, F_NaN => nan
           | F_NaN, _ => if is0 sb y then one else nan
           | _, F_NaN => if fin sa && Qeq_bool x 1 then one else nan
           | _, _ =>
             if is0 sa x && neg sb y then Value_Err "zero raised to a negative power is undefined"
             else if neg sa x && fin sb && negb yint then dom
             else
               match sb with
               | F_PosInf | F_NegInf =>
                 let c := match sa with F_PosInf | F_NegInf => Gt | _ => Qcompare (Qabs x) 1 end in
                 match c, sb with
                 | Eq, _ => one
                 | Gt, F_PosInf | Lt, F_NegInf => pinf
                 | _, _ => zero
                 end
               | _ =>
                 match sa with
                 | F_PosInf => if is0 sb y then one else if neg sb y then zero else pinf
                 | F_NegInf =>
                   let odd := Z.odd (Qnum yred) in
                   if is0 sb y then one
                   else if neg sb y then (if odd then VF false (F_NegZero, Qc_of_Z 0) else zero)
                   else if odd then VF false (F_NegInf, Qc_of_Z 0) else pinf
                 | _ => match pow_c x y with Some r => VF false r | None => dom end
                 end
               end
           end
         | _, _ => bad
         end
  | _ => Value_Err "function does not exist"
  end.

Definition pg_clamp_scale (r : Z) (sc : nat) : nat := Z.to_nat (Z.min (Z.max (Z.max r (Z.of_nat sc)) 0) 1000).

(** [estimate_ln_dweight]: the decimal weight of [ln x] *)
Definition pg_ln_dweight (x : Q) : Z :=
  if Qle_bool (9 # 10) x && Qle_bool x (11 # 10) then
    (if Qeq_bool x 1 then 0 else dexp10 (Qminus x 1))
  else let l := Qabs.Qabs (ln_exact x) in
       let e := dexp10 l in
       (* the truncation of [log10 |ln x|] towards zero *)
       if Qle_bool 1 l then e else if Qeq_bool l (Qpower 10 e) then e else e + 1.

Definition pg_num_sqrt (q : Qc) (sc : nat) : value :=
  if Qc_lt_bool q (Qc_of_Z 0) then Value_Err "cannot take square root of a negative number"
  else let (w, _) := nbase_weight q in
       let r := pg_clamp_scale (16 - (2 * w + 1)) sc in
       let n := Qnum q in
       let d := Zpos (Qden q) in
       let m := isqrt ((n * pow10 (2 * r + 2)) / d) in
       VDec (Qcdiv (Qc_of_Z ((m + 5) / 10)) (Qc_pow10 r)) r r.

Definition pg_num_exp (q : Qc) (sc : nat) : value :=
  let v := Qmult (this q) (434294481903252 # 1000000000000000) in
  let v := Qmax (-2000) (Qmin 2000 v) in
  let r := pg_clamp_scale (16 - Z.quot (Qnum v) (Zpos (Qden v))) sc in
  match exp_exact (this q) with
  | Some e => VDec (dec_round (Q2Qc e) r) r r
  | None => Value_Err "value overflows numeric format"
  end.

Definition pg_num_log (b : Qc * nat) (x : Qc * nat) : value :=
  let (qb, sb) := b in
  let (qx, sx) := x in
  if Qc_le_bool qx (Qc_of_Z 0) || Qc_le_bool qb (Qc_of_Z 0) then
    (if Qc_is_zero qx || Qc_is_zero qb then Value_Err "cannot take logarithm of zero"
     else Value_Err "cannot take logarithm of a negative number")
  else if Qc_eq_bool qb (Qc_of_Z 1) then Value_Err "division by zero"
  else let rd := pg_ln_dweight (this qx) - pg_ln_dweight (this qb) in
       let r := pg_clamp_scale (16 - rd) (Nat.max sb sx) in
       VDec (dec_round (Q2Qc (Qdiv (ln_exact (this qx)) (ln_exact (this qb)))) r) r r.

Definition pg_num_ln (q : Qc) (sc : nat) : value :=
  if Qc_le_bool q (Qc_of_Z 0) then
    (if Qc_is_zero q then Value_Err "cannot take logarithm of zero" else Value_Err "cannot take logarithm of a negative number")
  else let r := pg_clamp_scale (16 - pg_ln_dweight (this q)) sc in
       VDec (dec_round (Q2Qc (ln_exact (this q))) r) r r.

(** a function with a [numeric] and a [double precision] version: an integer argument takes the
    double one, the preferred type of the numeric category *)
Definition pg_num_or_dbl (fnum : Qc -> nat -> value) (fdbl : list value -> value) (l : list value) : value :=
  match l with
  | Value_D (Some (q, _, sc)) :: nil => fnum q sc
  | Value_D None :: nil => Value_D None
  | _ => fdbl l
  end.

Definition pg_dom (msg : string) : value := Value_Err msg.

(** the special values of the doubles in PostgreSQL ([float.c]) *)
Definition pg_sp_same (s : fspecial) : value := VF false (s, Qc_of_Z 0).
Definition pg_sp_range (s : fspecial) : value :=
  match s with F_NaN => VF false (F_NaN, Qc_of_Z 0) | _ => Value_Err "input is out of range" end.

(** [dexp]: an overflow and an underflow are errors *)
Definition pg_exp_dbl (q : Q) : option (fspecial * Qc) := Some (exp_q binary64 q).
Definition pg_exp_check (v : value) : value :=
  match v with
  | Value_F (Some (x, k)) =>
    match special_of_tag (Nat.div (Nat.modulo k 10) 2) with
    | F_PosInf => Value_Err "value out of range: overflow"
    | F_Finite => if Qc_is_zero x then Value_Err "value out of range: underflow" else v
    | _ => v
    end
  | _ => v
  end.

Definition pg_math_table (num_power : list value -> value) : list (string * (list value -> value)) :=
  let c := num_of_value in
  let bad := Value_Err "function does not exist" in
  let ln_dom := fun q => if Z.leb (Qnum q) 0 then None else Some (round_q binary64 (ln_exact q)) in
  let ln_err (l : list value) (v : value) :=
      match v, l with
      | Value_Err _, a :: nil => match math_arg c a with
                                 | Some (_, q) => if Z.eqb (Qnum q) 0 then Value_Err "cannot take logarithm of zero"
                                                  else Value_Err "cannot take logarithm of a negative number"
                                 | None => v end
      | _, _ => v
      end in
  let dln l := ln_err l (dbl_fun1 c ln_dom (Value_Err "log") (fun s => match s with F_NegInf => Value_Err "log" | _ => pg_sp_same s end) bad l) in
  let dlog10 l := ln_err l (dbl_fun1 c (fun q => log2_c 10 q) (Value_Err "log") (fun s => match s with F_NegInf => Value_Err "log" | _ => pg_sp_same s end) bad l) in
  let dsqrt := dbl_fun1 c (fun q => if Z.ltb (Qnum q) 0 then None else Some (sqrt_q binary64 q))
                        (pg_dom "cannot take square root of a negative number")
                        (fun s => match s with F_NegInf => pg_dom "cannot take square root of a negative number" | _ => pg_sp_same s end) bad in
  (* [exp] of an infinity is not an overflow: [dexp] of [float.c] returns [Infinity] and [0] *)
  let dexp l := match l with
                | v :: nil => match math_arg c v with
                              | Some (F_PosInf, _) => VF false (F_PosInf, Qc_of_Z 0)
                              | Some (F_NegInf, _) => VF false (F_Finite, Qc_of_Z 0)
                              | _ => pg_exp_check (dbl_fun1 c pg_exp_dbl bad (fun s => match s with F_NegInf => VF false (F_Finite, Qc_of_Z 0) | _ => pg_sp_same s end) bad l)
                              end
                | _ => pg_exp_check (dbl_fun1 c pg_exp_dbl bad (fun s => match s with F_NegInf => VF false (F_Finite, Qc_of_Z 0) | _ => pg_sp_same s end) bad l)
                end in
  let trig f := dbl_fun1 c (fun q => Some (f binary64 q)) bad pg_sp_range bad in
  let atrig (f : format -> Q -> option (fspecial * Qc)) := dbl_fun1 c (f binary64) (pg_dom "input is out of range") pg_sp_range bad in
  let dpow := pg_dpow c (pg_dom "a negative number raised to a non-integer power yields a complex result") bad in
  let numeric_log l := match l with
                       | b :: x :: nil =>
                         if is_null b || is_null x then Value_D None
                         else match dec_of_value b, dec_of_value x with
                              | Some (qb, _, sb), Some (qx, _, sx) => pg_num_log (qb, sb) (qx, sx)
                              | _, _ => bad end
                       | _ => bad end in
     ("sqrt", pg_num_or_dbl pg_num_sqrt dsqrt)
  :: ("cbrt", dbl_fun1 c (fun q => Some (cbrt_q binary64 q)) bad pg_sp_same bad)
  :: ("exp", pg_num_or_dbl pg_num_exp dexp)
  :: ("ln", pg_num_or_dbl pg_num_ln dln)
  :: ("log10", pg_num_or_dbl (fun q sc => pg_num_log (Qc_of_Z 10, 0%nat) (q, sc)) dlog10)
  :: ("log", fun l => match l with
                      | _ :: nil => pg_num_or_dbl (fun q sc => pg_num_log (Qc_of_Z 10, 0%nat) (q, sc)) dlog10 l
                      (* [log (b, x)] has only the [numeric] version *)
                      | _ => numeric_log l end)
  :: ("sin", trig sin_q) :: ("cos", trig cos_q) :: ("tan", trig tan_q)
  :: ("cot", dbl_fun1 c (fun q => let (s, c') := fp_sin_cos (fp_of_q q) in Some (round_q binary64 (Qdiv (q_of_fp c') (q_of_fp s)))) bad pg_sp_range bad)
  :: ("asin", atrig asin_q) :: ("acos", atrig acos_q)
  :: ("atan", dbl_fun1 c (fun q => Some (atan_q binary64 q)) bad
                (fun s => match s with F_PosInf => VF false (round_q binary64 (Qdiv pi_q 2))
                                  | F_NegInf => VF false (round_q binary64 (Qopp (Qdiv pi_q 2))) | _ => pg_sp_same s end) bad)
  :: ("atan2", dbl_fun2 c (fun y x => Some (atan2_q binary64 y x)) bad bad)
  :: ("sinh", dbl_fun1 c (fun q => Some (hyp_q binary64 0 q)) bad pg_sp_same bad)
  :: ("cosh", dbl_fun1 c (fun q => Some (hyp_q binary64 1 q)) bad (fun s => match s with F_NegInf => pg_sp_same F_PosInf | _ => pg_sp_same s end) bad)
  :: ("tanh", dbl_fun1 c (fun q => Some (hyp_q binary64 2 q)) bad
                (fun s => match s with F_PosInf => VF false (F_Finite, Qc_of_Z 1) | F_NegInf => VF false (F_Finite, Qc_of_Z (-1)) | _ => pg_sp_same s end) bad)
  :: ("degrees", dbl_fun1 c (fun q => Some (degrees_pg q)) bad pg_sp_same bad)
  :: ("radians", dbl_fun1 c (fun q => Some (radians_pg q)) bad pg_sp_same bad)
  :: ("pi", fun l => match l with nil => VF false (F_Finite, pi_double) | _ => bad end)
  (* [power] of two non-[numeric] arguments is the one of [double precision] *)
  :: ("power", fun l => if existsb is_D l then num_power l
                        else dpow l)
  :: nil.

Definition symbol_table_raw : list (string * (list value -> value)) :=
  let plus := pg_tm2 false (pg_int2 Z.add (pg_flt2 "+" Qcplus (pg_dec2 pg_dec_plus (arith2 (fun a b => Some (a + b)%Z) (fun a b => Some (Qcplus a b)))))) in
  let minus := pg_tm2 true (pg_int2 Z.sub (pg_flt2 "-" Qcminus (pg_dec2 pg_dec_minus (arith2 (fun a b => Some (a - b)%Z) (fun a b => Some (Qcminus a b)))))) in
  let mult := pg_int2 Z.mul (pg_flt2 "*" Qcmult (pg_dec2 pg_dec_mult (arith2 (fun a b => Some (a * b)%Z) (fun a b => Some (Qcmult a b))))) in
  let opp l := match l with
               | Value_D (Some (q, f, sc)) :: nil => VDec (Qcopp q) f sc
               | Value_F (Some (x, k)) :: nil => 
                 let w := Nat.odd k in
                 match special_of_tag (Nat.div (Nat.modulo k 10) 2) with
                 | F_Finite => if match Qccompare x (Q2Qc 0) with Eq => true | _ => false end 
                               then VF w (F_NegZero, x) else VF w (F_Finite, Qcopp x)
                 | F_NegZero => VF w (F_Finite, x)
                 | F_PosInf => VF w (F_NegInf, x)
                 | F_NegInf => VF w (F_PosInf, x)
                 | F_NaN => VF w (F_NaN, x)
                 end
               | _ => pg_int1 Z.opp (arith1 (fun a => Some (- a)%Z) (fun a => Some (Qcopp a))) l
               end in
  (* integer division truncates towards zero; division by zero is NULL *)
  (** division and modulo by zero are errors ([ERRCODE_DIVISION_BY_ZERO], [src/backend/utils/adt/int.c], [numeric.c]) *)
  let by_zero (f : list value -> value) (l : list value) :=
      match l with
      | a :: b :: nil => 
        (* a NaN divided by zero is NaN ([float8_div]) *)
        if match a with Value_F (Some (_, k)) => Nat.eqb (Nat.div (Nat.modulo k 10) 2) 4 | _ => false end then f l else
        match num_of_value b with
        | Some (Num_Z z) => if Z.eqb z 0 then Value_Err "division by zero" else f l
        | Some (Num_Q q) => if Qc_is_zero q then Value_Err "division by zero" else f l
        | _ => f l
        end
      | _ => f l
      end in
  let div := by_zero (pg_int2 Z.quot (pg_flt2 "/" Qcdiv (pg_dec2 pg_dec_div (arith2 (fun a b => if Z.eqb b 0 then None else Some (Z.quot a b))
                    (fun a b => if Qc_is_zero b then None else Some (Qcdiv a b)))))) in
  let modulo := by_zero (pg_int2 Z.rem (pg_dec2 pg_dec_mod (arith2 (fun a b => if Z.eqb b 0 then None else Some (Z.rem a b))
                       (fun _ _ => None)))) in
     ("plus", plus) :: ("+", plus)
  :: ("minus", minus) :: ("-", minus)
  :: ("mult", mult) :: ("*", mult)
  :: ("opp", opp) :: ("neg", opp)
  :: ("div", div) :: ("/", div)
  :: ("mod", modulo) :: ("%", modulo)
 :: ("abs", fun l => match l with
                      | Value_F (Some (x, k)) :: nil => 
                        let w := Nat.odd k in
                        match special_of_tag (Nat.div (Nat.modulo k 10) 2) with
                        | F_Finite => VF w (F_Finite, match Qccompare x (Q2Qc 0) with Lt => Qcopp x | _ => x end)
                        | F_NegZero => VF w (F_Finite, x)
                        | F_NegInf => VF w (F_PosInf, x)
                        | sp => VF w (sp, x)
                        end
                      | Value_D (Some (q, f, sc)) :: nil => 
                        VDec (match Qccompare q (Qc_of_Z 0) with Lt => Qcopp q | _ => q end) f sc
                      | _ => arith1 (fun a => Some (Z.abs a))
                    (fun a => Some (match Qccompare a (Qc_of_Z 0) with Lt => Qcopp a | _ => a end)) l end)
  :: ("sign", arith1 (fun a => Some (Z.sgn a))
                     (fun a => Some (Qc_of_Z (match Qccompare a (Qc_of_Z 0) with
                                              | Lt => (-1)%Z | Eq => 0%Z | Gt => 1%Z end))))
  :: ("power", arith2 Zpower_opt Qcpower_opt)
  :: ("floor", fun l => match l with
                        | Value_F (Some (x, k)) :: nil => 
                          if Nat.eqb (Nat.div (Nat.modulo k 10) 2) 0 then VF (Nat.odd k) (F_Finite, Qc_of_Z (Qc_floor x)) else Value_F (Some (x, k))
                        | Value_D (Some (q, _, _)) :: nil => VDec (Qc_of_Z (Qc_floor q)) 0 0
                        | Value_Q (Some q) :: nil => Value_Z (Some (Qc_floor q))
                        | Value_Z z :: nil => Value_Z z
                        | _ => Value_Z None end)
  :: ("ceil", fun l => match l with
                       | Value_F (Some (x, k)) :: nil => 
                         if Nat.eqb (Nat.div (Nat.modulo k 10) 2) 0 then VF (Nat.odd k) (F_Finite, Qc_of_Z (Qc_ceiling x)) else Value_F (Some (x, k))
                       | Value_D (Some (q, _, _)) :: nil => VDec (Qc_of_Z (Qc_ceiling q)) 0 0
                       | Value_Q (Some q) :: nil => Value_Z (Some (Qc_ceiling q))
                       | Value_Z z :: nil => Value_Z z
                       | _ => Value_Z None end)
  :: ("round", fun l => match l with
                        (* [round(float8)] is [rint]: ties to even *)
                        | Value_F (Some (x, k)) :: nil => 
                          if Nat.eqb (Nat.div (Nat.modulo k 10) 2) 0 
                          then VF (Nat.odd k) (F_Finite, Qc_of_Z (if Z.ltb (Qnum x) 0 
                                                                  then Z.opp (round_half_even (Z.opp (Qnum x)) (Zpos (Qden x)))
                                                                  else round_half_even (Qnum x) (Zpos (Qden x))))
                          else Value_F (Some (x, k))
                        | Value_D (Some (q, _, _)) :: nil => VDec (Qc_of_Z (Qc_round q)) 0 0
                        (* [round(x, d)]: a numeric of scale [d] ([numeric_round]) *)
                        | v :: Value_Z (Some d) :: nil => 
                          match dec_of_value v with
                          | Some (q, _, _) => 
                            if Z.leb 0 d then VDec (dec_round q (Z.to_nat d)) (Z.to_nat d) (Z.to_nat d)
                            else let m := Qc_of_Z (pow10 (Z.to_nat (Z.opp d))) in
                                 VDec (Qcmult (Qc_of_Z (Qc_round (Qcdiv q m))) m) 0 0
                          | None => Value_D None
                          end
                        | Value_Q (Some q) :: nil => Value_Z (Some (Qc_round q))
                        | Value_Z z :: nil => Value_Z z
                        | _ => Value_Z None end)
  :: ("trunc", fun l => match l with
                        | Value_D (Some (q, _, _)) :: nil => VDec (Qc_of_Z (Qc_trunc q)) 0 0
                        | v :: Value_Z (Some d) :: nil => 
                          match dec_of_value v with
                          | Some (q, _, _) => 
                            if Z.leb 0 d then VDec (dec_trunc q (Z.to_nat d)) (Z.to_nat d) (Z.to_nat d)
                            else let m := Qc_of_Z (pow10 (Z.to_nat (Z.opp d))) in
                                 VDec (Qcmult (Qc_of_Z (Qc_trunc (Qcdiv q m))) m) 0 0
                          | None => Value_D None
                          end
                        | Value_Q (Some q) :: nil => Value_Z (Some (Qc_trunc q))
                        | Value_Z z :: nil => Value_Z z
                        | _ => Value_Z None end)
  :: ("greatest", extremum is_Gt)
  :: ("least", extremum is_Lt)
  (* conditional expressions *)
  :: ("coalesce", coalesce)
  :: ("nullif", fun l => match l with
                         | v1 :: v2 :: nil =>
                           match sql_eq3 v1 v2 with
                           | true3 => default_value (type_of_value v1)
                           | _ => v1
                           end
                         | _ => Value_Z None end)
  :: ("case", sql_case)
  (* boolean connectives, on boolean values *)
  :: ("and", fun l => value_of_bool3
                        (fold_left (fun acc v => andb3 acc (bool3_of_value v)) l true3))
  :: ("or", fun l => value_of_bool3
                       (fold_left (fun acc v => orb3 acc (bool3_of_value v)) l false3))
  :: ("not", fun l => match l with
                      | v :: nil => value_of_bool3 (negb3 (bool3_of_value v))
                      | _ => Value_bool None end)
  (* strings *)
  :: ("||", fun l => match l with
                     | Value_string (Some s1) :: Value_string (Some s2) :: nil =>
                       Value_string (Some (s1 ++ s2))
                     | _ => Value_string None end)
  :: ("concat", concat_ws)
  :: ("length", strict_string1 (fun s => Value_Z (Some (Z.of_nat (String.length s)))))
  :: ("char_length", strict_string1 (fun s => Value_Z (Some (Z.of_nat (String.length s)))))
  :: ("upper", string_fun1 (string_map upper_ascii))
  :: ("lower", string_fun1 (string_map lower_ascii))
  :: ("trim", string_fun1 (fun s => string_rtrim (string_ltrim s)))
  :: ("ltrim", string_fun1 string_ltrim)
  :: ("rtrim", string_fun1 string_rtrim)
  :: ("reverse", string_fun1 string_rev)
  :: ("substring", fun l => match l with
                            | Value_string (Some s) :: Value_Z (Some i) :: nil =>
                              Value_string (Some (sql_substring s i None))
                            | Value_string (Some s) :: Value_Z (Some i) :: Value_Z (Some n) :: nil =>
                              if (n <? 0)%Z then Value_string None
                              else Value_string (Some (sql_substring s i (Some n)))
                            | _ => Value_string None end)
  :: ("left", fun l => match l with
                       | Value_string (Some s) :: Value_Z (Some n) :: nil =>
                         Value_string (Some (String.substring 0 (Z.to_nat n) s))
                       | _ => Value_string None end)
  :: ("right", fun l => match l with
                        | Value_string (Some s) :: Value_Z (Some n) :: nil =>
                          let k := Nat.min (Z.to_nat n) (String.length s) in
                          Value_string (Some (String.substring (String.length s - k) k s))
                        | _ => Value_string None end)
  :: ("replace", fun l => match l with
                          | Value_string (Some s) :: Value_string (Some from)
                                                  :: Value_string (Some to) :: nil =>
                            Value_string (Some (string_replace s from to))
                          | _ => Value_string None end)
  :: ("repeat", fun l => match l with
                         | Value_string (Some s) :: Value_Z (Some n) :: nil =>
                           Value_string (Some (string_repeat (Z.to_nat n) s))
                         | _ => Value_string None end)
  (* POSITION (sub IN s): 1-based, 0 when [sub] does not occur in [s] *)
  :: ("position", fun l => match l with
                           | Value_string (Some sub) :: Value_string (Some s) :: nil =>
                             Value_Z (Some (match String.index 0 sub s with
                                            | Some i => Z.of_nat (S i)
                                            | None => 0%Z
                                            end))
                           | _ => Value_Z None end)
  (* casts *)
  (* [integer] ([int4]), [smallint], [bigint]: the value must be in the range of the type *)
  :: ("cast_int", fun l => match l with 
                           | v :: nil => match cast_Z (widen v) with
                                         | Value_Z (Some z) => if int_range_ok 32 z then VInt 32 z else pg_int_error 32
                                         | Value_Z None => Value_I None
                                         | r => r end
                           | _ => Value_I None end)
  :: ("cast_smallint", fun l => match l with 
                                | v :: nil => match cast_Z (widen v) with
                                              | Value_Z (Some z) => if int_range_ok 16 z then VInt 16 z else pg_int_error 16
                                              | Value_Z None => Value_I None
                                              | r => r end
                                | _ => Value_I None end)
  :: ("cast_bigint", fun l => match l with 
                              | v :: nil => match cast_Z (widen v) with
                                            | Value_Z (Some z) => if int_range_ok 64 z then VInt 64 z else pg_int_error 64
                                            | r => r end
                              | _ => Value_Z None end)
  :: ("cast_numeric", fun l => match l with v :: nil => cast_Q v | _ => Value_Q None end)
  :: ("cast_string", fun l => match l with v :: nil => cast_string v | _ => Value_string None end)
  :: ("cast_bool", fun l => match l with v :: nil => cast_bool v | _ => Value_bool None end)
  (* [CAST(x AS numeric(p, s))]: rounded to [s] decimals, ties away from zero; an error when the
     integral part has more than [p - s] digits ([apply_typmod] in [numeric.c]) *)
  :: ("cast_decimal", fun l => match l with
                               | v :: Value_Z (Some p) :: Value_Z (Some sc) :: nil =>
                                 match dec_of_value (widen (match v with Value_F _ => cast_Q v | _ => v end)) with
                                 | Some (q, _, _) =>
                                   let s' := Z.to_nat sc in
                                   let r := dec_round q s' in
                                   if match Qccompare (Qc_of_Z (Z.abs (Qc_trunc r))) (Qc_of_Z (Z.pow 10 (p - sc))) with Lt => true | _ => false end
                                   then VDec r s' s' else Value_Err "numeric field overflow"
                                 | None => Value_D None
                                 end
                               | _ => Value_D None end)
  (* [x COLLATE "C"]: the only collation of the model is the byte order of [C] (and [POSIX]); the
     collations of the operating system and of ICU are not modelled *)
  :: ("collate", fun l => match l with
                          | Value_string s :: Value_string (Some n) :: nil =>
                            if (String.eqb n "C" || String.eqb n "POSIX" || String.eqb n "default")%bool 
                            then Value_string s else Value_Err "collation not modelled"
                          | _ => Value_string None end)
  (* JSON *)
  :: ("cast_jsonb", fun l => match l with 
                             | Value_string (Some t) :: nil => match parse_json t with Some j => VJ 0 j | None => Value_Err "invalid input syntax for type json" end
                             | Value_J (Some (t, _)) :: nil => match parse_json t with Some j => VJ 0 j | None => Value_J None end
                             | _ => Value_J None end)
  :: ("cast_json", fun l => match l with 
                            | Value_string (Some t) :: nil => match parse_json t with Some _ => Value_J (Some (t, 1%nat)) | None => Value_Err "invalid input syntax for type json" end
                            | Value_J (Some (t, _)) :: nil => Value_J (Some (t, 1%nat))
                            | _ => Value_J None end)
  :: ("->", fun l => match l with j :: k :: nil => pg_json_get false j (widen k) | _ => Value_J None end)
  :: ("->>", fun l => match l with j :: k :: nil => pg_json_get true j (widen k) | _ => Value_string None end)
  :: ("#>", fun l => match l with j :: p :: nil => pg_json_path false j p | _ => Value_J None end)
  :: ("#>>", fun l => match l with j :: p :: nil => pg_json_path true j p | _ => Value_string None end)
  :: ("jsonb_typeof", fun l => match l with j :: nil => match json_of_J j with Some d => Value_string (Some (pg_json_typeof d)) | None => Value_string None end | _ => Value_string None end)
  :: ("json_typeof", fun l => match l with j :: nil => match json_of_J j with Some d => Value_string (Some (pg_json_typeof d)) | None => Value_string None end | _ => Value_string None end)
  :: ("jsonb_array_length", fun l => match l with j :: nil => match json_of_J j with Some (JArr a) => Value_Z (Some (Z.of_nat (List.length a))) | Some _ => Value_Err "cannot get array length of a non-array" | None => Value_Z None end | _ => Value_Z None end)
  :: ("json_array_length", fun l => match l with j :: nil => match json_of_J j with Some (JArr a) => Value_Z (Some (Z.of_nat (List.length a))) | Some _ => Value_Err "cannot get array length of a non-array" | None => Value_Z None end | _ => Value_Z None end)
  :: ("jsonb_build_object", fun l => match pairs_of (map widen l) with Some ps => VJ 0 (JObj ps) | None => Value_Err "argument list must have even number of elements" end)
  :: ("json_build_object", fun l => match pairs_of (map widen l) with Some ps => VJ 1 (JObj ps) | None => Value_Err "argument list must have even number of elements" end)
  :: ("jsonb_build_array", fun l => VJ 0 (JArr (map pg_json_of_value l)))
  :: ("json_build_array", fun l => VJ 1 (JArr (map pg_json_of_value l)))
  :: ("to_jsonb", fun l => match l with v :: nil => VJ 0 (pg_json_of_value v) | _ => Value_J None end)
  :: ("to_json", fun l => match l with v :: nil => VJ 1 (pg_json_of_value v) | _ => Value_J None end)
  (* dates and times *)
  :: ("cast_date", fun l => match l with v :: nil => pg_cast_temporal 0 v | _ => Value_T None end)
  :: ("cast_time", fun l => match l with v :: nil => pg_cast_temporal 1 v | _ => Value_T None end)
  :: ("cast_timestamp", fun l => match l with v :: nil => pg_cast_temporal 2 v | _ => Value_T None end)
  :: ("cast_timestamptz", fun l => match l with v :: nil => pg_cast_temporal 3 v | _ => Value_T None end)
  :: ("cast_interval", fun l => match l with v :: nil => cast_interval v | _ => Value_V None end)
  :: ("extract", fun l => match l with Value_string (Some f) :: v :: nil => pg_extract f v | _ => Value_D None end)
  :: ("date_part", fun l => match l with 
                            | Value_string (Some f) :: v :: nil => 
                              match pg_extract f v with Value_D (Some (q, _, _)) => to_float false q | r => r end 
                            | _ => Value_F None end)
  :: ("date_trunc", fun l => match l with Value_string (Some f) :: v :: nil => pg_date_trunc f v | _ => Value_T None end)
  :: ("to_char", fun l => match l with 
                          | v :: Value_string (Some fmt) :: nil => 
                            match to_ts v with Some t => Value_string (Some (pg_format (S (String.length fmt)) t fmt)) 
                                          | None => if is_null v then Value_string None else Value_Err "function does not exist" end
                          | _ => Value_string None end)
  :: ("make_date", fun l => match map int_of l with
                            | Some y :: Some m :: Some d :: nil => 
                              if valid_date y m d then VDate (days_from_civil y m d) else Value_Err "date field value out of range"
                            | _ => Value_T None end)
  (* the time of the statement ([Temporal.statement_time]) *)
  :: ("now", fun _ => VTsTz statement_time 6) :: ("current_timestamp", fun _ => VTsTz statement_time 6)
  :: ("current_date", fun _ => VDate (ts_days statement_time))
  :: ("localtimestamp", fun _ => VTs statement_time 6)
  :: ("cast_float8", fun l => match l with v :: nil => cast_float false v | _ => Value_F None end)
  :: ("cast_float4", fun l => match l with v :: nil => cast_float true v | _ => Value_F None end)
  :: nil.

(** A function symbol which is not in the table of functions, but which is the
    name of a predicate, is that predicate seen as a boolean-valued function:
    this is what allows conditions to occur inside expressions, for instance as
    the guards of a CASE. Any other symbol yields NULL. *)
(** the functions whose result depends on the width of their integer arguments: the arithmetic, the
    casts, and the functions which return one of their arguments *)
(** ** Integers and bits in PostgreSQL ([int.c], [int8.c], [numeric.c])

    [&], [|], [#] (exclusive or) and [~] keep the (wider) integer type; [<<] and [>>] shift in the type of
    the left operand as C does (the bits shifted out are lost, the count is taken modulo the width).
    [gcd] and [lcm] of integers are integers (an [lcm] out of range is an error), of [numeric] values
    [numeric] with the larger scale; [factorial] is a [numeric]; [width_bucket] an [integer]. *)
Definition wrap_width (w : nat) (z : Z) : Z :=
  let b := Z.of_nat (if Nat.eqb w 1 then 64 else w) in
  let u := Z.modulo z (2 ^ b) in
  if Nat.eqb w 1 then u else if Z.leb (2 ^ (b - 1)) u then u - 2 ^ b else u.

Definition pg_bit2 (f : Z -> Z -> Z) (l : list value) : value :=
  match l with
  | v1 :: v2 :: nil =>
    match int_parts v1, int_parts v2 with
    | Some (a, w1), Some (b, w2) => VInt (Nat.max w1 w2) (f a b)
    | _, _ => if is_null v1 || is_null v2 then Value_Z None else Value_Err "operator does not exist"
    end
  | _ => Value_Err "operator does not exist"
  end.

Definition pg_shift (left : bool) (l : list value) : value :=
  match l with
  | v1 :: v2 :: nil =>
    match int_parts v1, int_parts v2 with
    | Some (a, w), Some (n, _) =>
      let wd := Z.of_nat w in
      let n := Z.modulo n wd in
      VInt w (wrap_width w (if left then Z.shiftl a n else Z.shiftr a n))
    | _, _ => if is_null v1 || is_null v2 then Value_Z None else Value_Err "operator does not exist"
    end
  | _ => Value_Err "operator does not exist"
  end.

Definition pg_gcd_lcm (lcm : bool) (l : list value) : value :=
  match l with
  | v1 :: v2 :: nil =>
    if is_null v1 || is_null v2 then (if is_D v1 || is_D v2 then Value_D None else Value_Z None)
    else match int_parts v1, int_parts v2 with
         | Some (a, w1), Some (b, w2) =>
           let w := Nat.max w1 w2 in
           let g := Z.gcd a b in
           let r := if lcm then (if Z.eqb g 0 then 0 else Z.abs (Z.quot a g * b)) else g in
           if int_range_ok w r then VInt w r else pg_int_error w
         | _, _ =>
           match dec_of_value v1, dec_of_value v2 with
           | Some (a, _, s1), Some (b, _, s2) =>
             let sc := Nat.max s1 s2 in
             let ia := Qc_round (Qcmult a (Qc_pow10 sc)) in
             let ib := Qc_round (Qcmult b (Qc_pow10 sc)) in
             let g := Z.gcd ia ib in
             let r := if lcm then (if Z.eqb g 0 then 0 else Z.abs (Z.quot ia g * ib)) else g in
             (* the [lcm] of the scaled integers is scaled once more *)
             let q := if lcm then Qcdiv (Qc_of_Z r) (Qcmult (Qc_pow10 sc) (Qc_pow10 sc)) else Qcdiv (Qc_of_Z r) (Qc_pow10 sc) in
             let q := if lcm then Qcmult q (Qc_pow10 sc) else q in
             VDec q sc sc
           | _, _ => Value_Err "function does not exist"
           end
         end
  | _ => Value_Err "function does not exist"
  end.

Fixpoint fact_nat (n : nat) : Z := match n with O => 1 | S k => Z.of_nat n * fact_nat k end.

Definition pg_factorial (l : list value) : value :=
  match l with
  | v :: nil =>
    match int_parts v with
    | Some (n, _) => if Z.ltb n 0 then Value_Err "factorial of a negative number is undefined"
                     else if Z.ltb 32177 n then Value_Err "value overflows numeric format"
                     else VDec (Qc_of_Z (fact_nat (Z.to_nat n))) 0 0
    | None => if is_null v then Value_D None else Value_Err "function does not exist"
    end
  | _ => Value_Err "function does not exist"
  end.

(** [width_bucket (operand, low, high, count)] ([width_bucket_numeric], [width_bucket_float8]) *)
Definition pg_width_bucket (l : list value) : value :=
  match l with
  | op :: b1 :: b2 :: cnt :: nil =>
    if existsb is_null l then Value_I None
    else match num_of_value op, num_of_value b1, num_of_value b2, int_parts cnt with
         | Some o, Some lo, Some hi, Some (c, _) =>
           let q n := match n with Num_Z z => inject_Z z | Num_Q q => this q end in
           let o := q o in let lo := q lo in let hi := q hi in
           if Z.leb c 0 then Value_Err "count must be greater than zero"
           else if Qeq_bool lo hi then Value_Err "lower bound cannot equal upper bound"
           else let fl x := Qfloor x in
                let r := if negb (Qle_bool hi lo) then
                           (if negb (Qle_bool lo o) then 0 else if Qle_bool hi o then c + 1
                            else fl (Qdiv (Qmult (Qminus o lo) (inject_Z c)) (Qminus hi lo)) + 1)
                         else
                           (if negb (Qle_bool o lo) then 0 else if Qle_bool o hi then c + 1
                            else fl (Qdiv (Qmult (Qminus lo o) (inject_Z c)) (Qminus lo hi)) + 1) in
                if int_range_ok 32 r then VInt 32 r else Value_Err "integer out of range"
         | _, _, _, _ => Value_Err "function does not exist"
         end
  | _ => Value_Err "function does not exist"
  end.

Definition pg_int_table : list (string * (list value -> value)) :=
     ("&", pg_bit2 Z.land) :: ("|", pg_bit2 Z.lor) :: ("#", pg_bit2 Z.lxor)
  :: ("~", fun l => match l with
                    | v :: nil => match int_parts v with Some (a, w) => VInt w (Z.lnot a) | None => Value_Z None end
                    | _ => Value_Err "operator does not exist" end)
  :: ("<<", pg_shift true) :: (">>", pg_shift false)
  :: ("gcd", pg_gcd_lcm false) :: ("lcm", pg_gcd_lcm true)
  :: ("factorial", pg_factorial)
  :: ("width_bucket", pg_width_bucket)
  :: nil.

Definition width_names : list string :=
  "+" :: "-" :: "*" :: "/" :: "%" :: "plus" :: "minus" :: "mult" :: "div" :: "mod" :: "opp" :: "neg"
      :: "cast_int" :: "cast_smallint" :: "cast_bigint" :: "coalesce" :: "nullif" :: "greatest" :: "least" :: "case"
      :: "&" :: "|" :: "#" :: "~" :: "<<" :: ">>" :: "gcd" :: "lcm" :: "factorial" :: "width_bucket" :: nil.

Definition symbol_table : list (string * (list value -> value)) :=
  map (fun p => if existsb (String.eqb (fst p)) width_names then p else (fst p, fun l => (snd p) (map widen l)))
      (pg_int_table ++ pg_math_table (match string_assoc _ "power" symbol_table_raw with Some g => g | None => fun _ => Value_Z None end)
       (* [ceiling] is [ceil]; [random ()] is not deterministic and is not modelled *)
       ++ ("ceiling", match string_assoc _ "ceil" symbol_table_raw with Some g => g | None => fun _ => Value_Z None end)
       :: ("random", fun _ => Value_Err "nondeterministic function")
       :: symbol_table_raw).

Definition interp_symbol f : list value -> value :=
  match f with
    | Symbol _ s =>
      match string_assoc _ s symbol_table with
      | Some g => g
      | None =>
        match string_assoc _ s predicate_table with
        | Some p => fun l => value_of_bool3 (p (map widen l))
        | None => fun _ => Value_Z None
        end
      end
    | CstVal _ v =>
      fun l =>
        match l with
          | nil => v
          | _ => default_value (type_of_value v)
        end
  end.

(** * Interpretation of aggregates

    Except for COUNT( * ), aggregates ignore NULLs. Except for the two COUNT, the
    aggregate of an empty collection (or of a collection of NULLs) is NULL. *)

Definition non_nulls (l : list value) := filter (fun v => negb (is_null v)) l.

(** The NULL of the type of the values in [l]; the type of an empty collection
    is not known, and defaults to integer. *)
Definition null_like (l : list value) :=
  match l with
  | v :: _ => default_value (type_of_value v)
  | nil => Value_Z None
  end.

Fixpoint value_dedup (l : list value) :=
  match l with
  | nil => nil
  | v :: l => v :: filter (fun v' => negb (value_eqb v v')) (value_dedup l)
  end.

Definition value_plus v1 v2 :=
  pg_flt2 "+" Qcplus (pg_dec2 pg_dec_plus (arith2 (fun a b => Some (a + b)%Z) (fun a b => Some (Qcplus a b)))) (v1 :: v2 :: nil).

Definition agg_sum (l : list value) :=
  match non_nulls l with
  | nil => null_like l
  | v :: l' => fold_left value_plus l' v
  end.

(** [avg] of integers or numerics is a numeric: the quotient of the sum by the count, with the
    scale of [select_div_scale] ([numeric_avg], [int8_avg] in [numeric.c]) *)
Definition agg_avg (l : list value) :=
  let nn := non_nulls l in
  match nn with
  | nil => Value_D None
  | _ =>
    match agg_sum nn with
    (* [avg] of floats is a [float8] ([float8_avg], [float4_accum]) *)
    | Value_F (Some (x, k)) => 
      pg_flt2 "/" Qcdiv (fun _ => Value_F None) (Value_F (Some (x, (2 * Nat.div (Nat.modulo k 10) 2)%nat)) :: Value_Z (Some (Z.of_nat (List.length nn))) :: nil)
    | sm => 
    match dec_of_value sm with
    | Some (q, _, sc) => pg_dec_div (q, sc) (Qc_of_Z (Z.of_nat (List.length nn)), 0%nat)
    | None => Value_D None
    end
    end
  end.

Definition agg_extremum (keep : comparison -> bool) (l : list value) :=
  match non_nulls l with
  | nil => null_like l
  | v :: l' => fold_left (pick keep) l' v
  end.

Definition agg_bool (op : bool -> bool -> bool) (l : list value) :=
  match non_nulls l with
  | Value_bool (Some b) :: l' =>
    Value_bool (Some (fold_left (fun acc v => match v with
                                              | Value_bool (Some b) => op acc b
                                              | _ => acc
                                              end) l' b))
  | _ => Value_bool None
  end.

Definition agg_string (sep : string) (l : list value) :=
  match non_nulls l with
  | Value_string (Some s) :: l' =>
    Value_string (Some (fold_left (fun acc v => match v with
                                                | Value_string (Some s) => acc ++ sep ++ s
                                                | _ => acc
                                                end) l' s))
  | _ => Value_string None
  end.

(** Population and sample variance, computed exactly. *)
Definition agg_var (sample : bool) (l : list value) :=
  let nn := non_nulls l in
  let n := Qc_of_Z (Z.of_nat (List.length nn)) in
  let sq := map (fun v => arith2 (fun a b => Some (a * b)%Z) (fun a b => Some (Qcmult a b))
                                 (v :: v :: nil)) nn in
  match nn, num_of_value (agg_sum nn), num_of_value (agg_sum sq) with
  | _ :: _, Some s, Some s2 =>
    let s := Qc_of_num s in
    let s2 := Qc_of_num s2 in
    let num := Qcminus s2 (Qcdiv (Qcmult s s) n) in
    let den := if sample then Qcminus n (Qc_of_Z 1) else n in
    if Qc_is_zero den then Value_Q None else Value_Q (Some (Qcdiv num den))
  | _, _, _ => Value_Q None
  end.

Definition agg_bit (op : Z -> Z -> Z) (l : list value) :=
  match non_nulls l with
  | Value_Z (Some z) :: l' =>
    Value_Z (Some (fold_left (fun acc v => match v with
                                           | Value_Z (Some z) => op acc z
                                           | _ => acc
                                           end) l' z))
  | _ => Value_Z None
  end.

Definition aggregate_table : list (string * (list value -> value)) :=
     ("count", fun l => Value_Z (Some (Z.of_nat (List.length (non_nulls l)))))
  :: ("count(*)", fun l => Value_Z (Some (Z.of_nat (List.length l))))
  :: ("sum", agg_sum)
  :: ("avg", agg_avg)
  :: ("min", agg_extremum is_Lt)
  :: ("max", agg_extremum is_Gt)
  :: ("bool_and", agg_bool andb)
  :: ("every", agg_bool andb)
  :: ("bool_or", agg_bool orb)
  :: ("string_agg", agg_string "")
  :: ("group_concat", agg_string ",")
  :: ("var_pop", agg_var false)
  :: ("var_samp", agg_var true)
  :: ("variance", agg_var true)
  :: ("bit_and", agg_bit Z.land)
  :: ("bit_or", agg_bit Z.lor)
  :: nil.

(** An aggregate name of the form ["distinct f"] is the aggregate ["f"] applied
    after duplicate elimination, that is [f(DISTINCT e)]. *)
Definition interp_aggregate a (l : list value) :=
  match a with
  | Aggregate s =>
    let (s', l') :=
        if String.prefix "distinct " s
        then (String.substring 9 (String.length s - 9) s, value_dedup l)
        else (s, l) in
    match string_assoc _ s' aggregate_table with
    (* [min] and [max] keep the type; [sum] of [smallint] and [integer] is a [bigint] *)
    | Some f => f (if (String.eqb s' "min" || String.eqb s' "max")%bool then l' else map widen l')
    | None => Value_Z None
    end
  end.

End NullValues.
(*
(** Embedding several coq datatypes (corresponding to domains) into a single uniform
    type for values.
*)
Inductive value : Set :=
  | Value_string : string -> value
  | Value_Z : Z -> value
  | Value_bool : bool -> value.

Definition type_of_value v := 
match v with
  | Value_string _  => type_string
  | Value_Z _ => type_Z
  | Value_bool _ => type_bool
  end.

(** Default values for each type. *)
Definition default_value d :=
  match d with
    | type_string => Value_string EmptyString
    | type_Z => Value_Z 0
    | type_bool => Value_bool false
  end.

(** injection of domain names into natural numbers in order to
    build an ordering on them.
*)

(** Comparison over values, in order to build an ordered type over values, and then
    finite sets.
*)
Definition value_compare x y := 
  match x, y with
    | Value_string s1, Value_string s2 => string_compare s1 s2
    | Value_string _, _ => Lt 
    | Value_Z _, Value_string _ => Gt
    | Value_Z z1, Value_Z z2 => Z.compare z1 z2
    | Value_Z _, _ => Lt
    | Value_bool _, Value_string _ => Gt
    | Value_bool _, Value_Z _ => Gt
    | Value_bool b1, Value_bool b2 => bool_compare b1 b2
  end.

Definition OVal : Oset.Rcd value.
split with value_compare.
- (* 1/3 *)
  intros [s1 | z1 | b1] [s2 | z2 | b2]; try discriminate.
  + generalize (Oset.eq_bool_ok Ostring s1 s2); simpl; case (string_compare s1 s2).
    * apply f_equal.
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok OZ z1 z2); simpl; case (Z.compare z1 z2).
    * apply f_equal.
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok Obool b1 b2); simpl; case (bool_compare b1 b2).
    * apply f_equal.
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
- (* 1/2 *)
  intros [s1 | z1 | b1] [s2 | z2 | b2] [s3 | z3 | b3]; trivial; try discriminate; simpl.
  + apply (Oset.compare_lt_trans Ostring).
  + apply (Oset.compare_lt_trans OZ).
  + apply (Oset.compare_lt_trans Obool).
- (* 1/1 *)
  intros [s1 | z1 | b1] [s2 | z2 | b2]; trivial; simpl.
  + apply (Oset.compare_lt_gt Ostring).
  + apply (Oset.compare_lt_gt OZ).
  + apply (Oset.compare_lt_gt Obool).
Defined.

Definition FVal := Fset.build OVal.
*)
