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

Require Import Arith NArith ZArith String List Ascii QArith Qcanon Qround DecimalString.
Require Import OrderedSet FiniteSet Bool3 IEEE.

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
  | Value_I : option (Z * nat) -> value.

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
  | Value_I None => true
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
    | _, _ => N.compare (value_rank x) (value_rank y)
  end.

Definition OVal : Oset.Rcd value.
split with value_compare.
- (* 1/3 *)
  intros [[s1 | ] | [z1 | ] | [b1 | ] | [q1 | ] | e1 | [d1 | ] | [f1 | ] | [i1 | ]] [[s2 | ] | [z2 | ] | [b2 | ] | [q2 | ] | e2 | [d2 | ] | [f2 | ] | [i2 | ]];
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
- (* 1/2 *)
  intros [[s1 | ] | [z1 | ] | [b1 | ] | [q1 | ] | e1 | [d1 | ] | [f1 | ] | [i1 | ]] [[s2 | ] | [z2 | ] | [b2 | ] | [q2 | ] | e2 | [d2 | ] | [f2 | ] | [i2 | ]]
         [[s3 | ] | [z3 | ] | [b3 | ] | [q3 | ] | e3 | [d3 | ] | [f3 | ] | [i3 | ]]; simpl; trivial; try discriminate.
  + apply (Oset.compare_lt_trans Ostring).
  + apply (Oset.compare_lt_trans OZ).
  + apply (Oset.compare_lt_trans Obool).
  + apply (Oset.compare_lt_trans OQc).
  + apply (Oset.compare_lt_trans Ostring).
  + apply (Oset.compare_lt_trans ODec).
  + apply (Oset.compare_lt_trans OFlt).
  + apply (Oset.compare_lt_trans OInt).
- (* 1/1 *)
  intros [[s1 | ] | [z1 | ] | [b1 | ] | [q1 | ] | e1 | [d1 | ] | [f1 | ] | [i1 | ]] [[s2 | ] | [z2 | ] | [b2 | ] | [q2 | ] | e2 | [d2 | ] | [f2 | ] | [i2 | ]];
    simpl; trivial.
  + apply (Oset.compare_lt_gt Ostring).
  + apply (Oset.compare_lt_gt OZ).
  + apply (Oset.compare_lt_gt Obool).
  + apply (Oset.compare_lt_gt OQc).
  + apply (Oset.compare_lt_gt Ostring).
  + apply (Oset.compare_lt_gt ODec).
  + apply (Oset.compare_lt_gt OFlt).
  + apply (Oset.compare_lt_gt OInt).
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
  | Value_F (Some (q, k)) => if Nat.leb (Nat.div k 2) 1 then Some (Num_Q q) else None
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
  | Value_F (Some (q, k)) => if Nat.leb (Nat.div k 2) 1 then Some (this q) else None
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

Definition Zpower_opt (a b : Z) : option Z :=
  match b with
  | Zneg _ => None
  | _ => Some (Z.pow a b)
  end.

Definition Qcpower_opt (a b : Qc) : option Qc :=
  (* only integral exponents are supported *)
  if Pos.eqb (Qden b) 1
  then match Qnum b with
       | Z0 => Some (Qc_of_Z 1)
       | Zpos p => Some (Qcpower a (Pos.to_nat p))
       | Zneg p => if Qc_is_zero a then None else Some (Qcinv (Qcpower a (Pos.to_nat p)))
       end
  else None.

(** * SQL comparison

    [sql_compare v1 v2] is [None] when one of the arguments is NULL, or when the
    two values are not comparable (a typing error in SQL); the comparison
    predicates are then UNKNOWN. *)
(** The order of the floats of PostgreSQL ([float8_cmp_internal]): -Infinity < the numbers < Infinity < NaN,
    and NaN is equal to NaN. *)
Definition float_rank (v : value) : option nat :=
  match v with
  | Value_F (Some (_, k)) => 
    match Nat.div k 2 with 2%nat => Some 2%nat | 3%nat => Some 0%nat | 4%nat => Some 3%nat | _ => Some 1%nat end
  | Value_Z (Some _) | Value_Q (Some _) | Value_D (Some _) | Value_I (Some _) => Some 1%nat
  | _ => None
  end.

Definition sql_compare v1 v2 : option comparison :=
  match v1, v2 with
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
  | Value_F (Some (x, k)) => Some (special_of_tag (Nat.div k 2), x, Nat.odd k)
  | _ => None
  end.

Definition is_F (v : value) : bool := match v with Value_F _ => true | _ => false end.
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
Definition pg_dec_div (a b : Qc * nat) := 
  let r := pg_div_scale (fst a) (snd a) (fst b) (snd b) in
  VDec (dec_round (Qcdiv (fst a) (fst b)) r) r r.

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
  | Value_F (Some (x, k)) => if w32 then VF true (round_q binary32 x) else Value_F (Some (x, (2 * Nat.div k 2)%nat))
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
     ("=", binary3 sql_eq3)
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

Definition symbol_table_raw : list (string * (list value -> value)) :=
  let plus := pg_int2 Z.add (pg_flt2 "+" Qcplus (pg_dec2 pg_dec_plus (arith2 (fun a b => Some (a + b)%Z) (fun a b => Some (Qcplus a b))))) in
  let minus := pg_int2 Z.sub (pg_flt2 "-" Qcminus (pg_dec2 pg_dec_minus (arith2 (fun a b => Some (a - b)%Z) (fun a b => Some (Qcminus a b))))) in
  let mult := pg_int2 Z.mul (pg_flt2 "*" Qcmult (pg_dec2 pg_dec_mult (arith2 (fun a b => Some (a * b)%Z) (fun a b => Some (Qcmult a b))))) in
  let opp l := match l with
               | Value_D (Some (q, f, sc)) :: nil => VDec (Qcopp q) f sc
               | Value_F (Some (x, k)) :: nil => 
                 let w := Nat.odd k in
                 match special_of_tag (Nat.div k 2) with
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
      | _ :: b :: nil => 
        match num_of_value b with
        | Some (Num_Z z) => if Z.eqb z 0 then Value_Err "division by zero" else f l
        | Some (Num_Q q) => if Qc_is_zero q then Value_Err "division by zero" else f l
        | _ => f l
        end
      | _ => f l
      end in
  let div := by_zero (pg_int2 Z.quot (pg_flt2 "/" Qcdiv (pg_dec2 pg_dec_div (arith2 (fun a b => if Z.eqb b 0 then None else Some (Z.quot a b))
                    (fun a b => if Qc_is_zero b then None else Some (Qcdiv a b)))))) in
  let modulo := by_zero (pg_int2 Z.rem (arith2 (fun a b => if Z.eqb b 0 then None else Some (Z.rem a b))
                       (fun _ _ => None))) in
     ("plus", plus) :: ("+", plus)
  :: ("minus", minus) :: ("-", minus)
  :: ("mult", mult) :: ("*", mult)
  :: ("opp", opp) :: ("neg", opp)
  :: ("div", div) :: ("/", div)
  :: ("mod", modulo) :: ("%", modulo)
 :: ("abs", fun l => match l with
                      | Value_F (Some (x, k)) :: nil => 
                        let w := Nat.odd k in
                        match special_of_tag (Nat.div k 2) with
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
                          if Nat.eqb (Nat.div k 2) 0 then VF (Nat.odd k) (F_Finite, Qc_of_Z (Qc_floor x)) else Value_F (Some (x, k))
                        | Value_D (Some (q, _, _)) :: nil => VDec (Qc_of_Z (Qc_floor q)) 0 0
                        | Value_Q (Some q) :: nil => Value_Z (Some (Qc_floor q))
                        | Value_Z z :: nil => Value_Z z
                        | _ => Value_Z None end)
  :: ("ceil", fun l => match l with
                       | Value_F (Some (x, k)) :: nil => 
                         if Nat.eqb (Nat.div k 2) 0 then VF (Nat.odd k) (F_Finite, Qc_of_Z (Qc_ceiling x)) else Value_F (Some (x, k))
                       | Value_D (Some (q, _, _)) :: nil => VDec (Qc_of_Z (Qc_ceiling q)) 0 0
                       | Value_Q (Some q) :: nil => Value_Z (Some (Qc_ceiling q))
                       | Value_Z z :: nil => Value_Z z
                       | _ => Value_Z None end)
  :: ("round", fun l => match l with
                        (* [round(float8)] is [rint]: ties to even *)
                        | Value_F (Some (x, k)) :: nil => 
                          if Nat.eqb (Nat.div k 2) 0 
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
  :: ("cast_float8", fun l => match l with v :: nil => cast_float false v | _ => Value_F None end)
  :: ("cast_float4", fun l => match l with v :: nil => cast_float true v | _ => Value_F None end)
  :: nil.

(** A function symbol which is not in the table of functions, but which is the
    name of a predicate, is that predicate seen as a boolean-valued function:
    this is what allows conditions to occur inside expressions, for instance as
    the guards of a CASE. Any other symbol yields NULL. *)
(** the functions whose result depends on the width of their integer arguments: the arithmetic, the
    casts, and the functions which return one of their arguments *)
Definition width_names : list string :=
  "+" :: "-" :: "*" :: "/" :: "%" :: "plus" :: "minus" :: "mult" :: "div" :: "mod" :: "opp" :: "neg"
      :: "cast_int" :: "cast_smallint" :: "cast_bigint" :: "coalesce" :: "nullif" :: "greatest" :: "least" :: "case" :: nil.

Definition symbol_table : list (string * (list value -> value)) :=
  map (fun p => if existsb (String.eqb (fst p)) width_names then p else (fst p, fun l => (snd p) (map widen l)))
      symbol_table_raw.

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
      pg_flt2 "/" Qcdiv (fun _ => Value_F None) (Value_F (Some (x, (2 * Nat.div k 2)%nat)) :: Value_Z (Some (Z.of_nat (List.length nn))) :: nil)
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
