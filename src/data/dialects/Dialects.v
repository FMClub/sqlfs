(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**                  The value semantics of the SQL dialects                        *)
(**                                                                                 *)
(************************************************************************************)

(** * Dialects

    The values, the predicates, the function symbols and the aggregates of all the
    dialects are the same _syntactic_ objects (those of [Values.v]); a dialect is a
    way to interpret them, together with the engine-level choices of the record
    [dialect] of [SqlFull.v]. [vsem] packages all of that; [TD d] is the instance of
    [Tuple.Rcd] which interprets the symbols as the dialect [d] does.

    All the instances [TD d] have the same types of values, attributes, and tuples,
    which reduce to the same types: a query written for one dialect can be run in any
    other by [to_dialect]. *)

Require Import List String ZArith NArith QArith Qcanon.

Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlFull.

Import Tuple.
Require Import Values TuplesImpl GenericInstance.

Close Scope Q_scope.
Close Scope Qc_scope.
Open Scope string_scope.

Definition value := NullValues.value.

(** * The value semantics of a dialect *)

Record vsem : Type :=
  mk_vsem
    {
      vs_name : string;
      (** predicates, function symbols and aggregates, by name; what is not in the
          tables is UNKNOWN for a predicate, NULL for a function, NULL for an aggregate *)
      vs_pred : string -> option (list value -> bool3);
      vs_symb : string -> option (list value -> value);
      vs_agg : string -> option (list value -> value);
      (** the fields of the record [dialect] of [SqlFull.v] *)
      vs_is_null : value -> bool;
      vs_truth : value -> bool3;
      vs_of_truth : bool3 -> value;
      vs_eq3 : value -> value -> bool3;
      vs_order : value -> value -> comparison;
      vs_canon : value -> value;
      vs_nulls_smallest : bool;
      vs_supports : feature -> bool
    }.

(** [DISTINCT] aggregates: the name of the aggregate starts with ["distinct "]. *)
Fixpoint dedup_values (canon : value -> value) (l : list value) : list value :=
  match l with
  | nil => nil
  | v :: l => 
    v :: filter (fun v' => negb (Oset.eq_bool NullValues.OVal (canon v) (canon v'))) 
                (dedup_values canon l)
  end.

Definition vs_interp_predicate (d : vsem) (p : Values.predicate) : list value -> bool3 :=
  match p with
  | Values.Predicate s => match vs_pred d s with Some f => f | None => fun _ => unknown3 end
  end.

Definition vs_interp_symbol (d : vsem) (f : Values.symbol value) : list value -> value :=
  match f with
  | Values.Symbol _ s =>
    match vs_symb d s with
    | Some g => g
    | None =>
      (* a predicate used as a function *)
      match vs_pred d s with
      | Some p => fun l => vs_of_truth d (p l)
      | None => fun _ => NullValues.Value_Z None
      end
    end
  | Values.CstVal _ v =>
    fun l => match l with nil => v | _ => NullValues.default_value (NullValues.type_of_value v) end
  end.

Definition vs_interp_aggregate (d : vsem) (a : Values.aggregate) (l : list value) : value :=
  match a with
  | Values.Aggregate s =>
    let (s', l') :=
        if String.prefix "distinct " s
        then (String.substring 9 (String.length s - 9) s, dedup_values (vs_canon d) l)
        else (s, l) in
    match vs_agg d s' with
    | Some f => f l'
    | None => NullValues.Value_Z None
    end
  end.

(** * The instance of [Tuple.Rcd] of a dialect *)

Definition TD (d : vsem) : Tuple.Rcd :=
  Tuple2.T attribute type NullValues.value 
           type_of_attribute 
           NullValues.type_of_value 
           NullValues.default_value 
           OAN FAN NullValues.OVal NullValues.FVal
           Values.predicate _ Values.aggregate OP (OSymbol _ NullValues.OVal) OAgg Bool3.Bool3
           (vs_interp_predicate d) (vs_interp_symbol d) (vs_interp_aggregate d).

Definition dialect_of (d : vsem) : dialect (TD d) :=
  mk_dialect (TD d)
             (vs_is_null d)
             (NullValues.Value_Z None)
             (vs_truth d)
             (vs_of_truth d)
             (vs_eq3 d)
             (vs_order d)
             (fun z => NullValues.Value_Z (Some z))
             (vs_canon d)
             (vs_nulls_smallest d)
             (vs_supports d).

(** * Moving a query to a dialect

    The queries of the tests are written with the instance [TNull] of [GenericInstance.v].
    The syntax is parameterised by the instance, but the types of what it contains
    do not depend on the interpretation, so that the transformation is the identity,
    up to the type. *)

Section Transport.

Variable d2 : vsem.
Hypothesis relname : Type.

Notation T1 := TNull.
Notation T2 := (TD d2).

Definition ren_to (r : SqlFull.renaming T1) : SqlFull.renaming T2 :=
  match r with
  | Ren_Star _ => Ren_Star T2
  | Ren_List _ l => Ren_List T2 l
  end.

Fixpoint sexpr_to (e : sexpr T1 relname) {struct e} : sexpr T2 relname :=
  match e with
  | E_Const _ _ v => E_Const T2 relname v
  | E_Col _ _ a => E_Col T2 relname a
  | E_Fun f l => @E_Fun T2 relname f (map sexpr_to l)
  | E_Agg ag sq e c => @E_Agg T2 relname ag sq (sexpr_to e) (scond_to c)
  | E_Case c e1 e2 => @E_Case T2 relname (scond_to c) (sexpr_to e1) (sexpr_to e2)
  | E_Cond c => @E_Cond T2 relname (scond_to c)
  | E_Sub q => @E_Sub T2 relname (squery_to q)
  end

with scond_to (c : scond T1 relname) {struct c} : scond T2 relname :=
  match c with
  | C_Conj a c1 c2 => @C_Conj T2 relname a (scond_to c1) (scond_to c2)
  | C_Not c => @C_Not T2 relname (scond_to c)
  | C_True _ _ => C_True T2 relname
  | C_Pred p l => @C_Pred T2 relname p (map sexpr_to l)
  | C_Expr e => @C_Expr T2 relname (sexpr_to e)
  | C_Quant qtf p l q la => @C_Quant T2 relname qtf p (map sexpr_to l) (squery_to q) la
  | C_In l q la => @C_In T2 relname (map sexpr_to l) (squery_to q) la
  | C_Exists q => @C_Exists T2 relname (squery_to q)
  end

with squery_to (q : squery T1 relname) {struct q} : squery T2 relname :=
  match q with
  | SQ_Table _ r => SQ_Table T2 r
  | SQ_Set o sq q1 q2 => @SQ_Set T2 relname o sq (squery_to q1) (squery_to q2)
  | SQ_Select sp => @SQ_Select T2 relname (sspec_to sp)
  | SQ_Order q lo off lim => @SQ_Order T2 relname (squery_to q) (map sorder_to lo) off lim
  | SQ_Window q lw => @SQ_Window T2 relname (squery_to q) (map swindow_to lw)
  | SQ_With r q1 q2 => @SQ_With T2 relname r (squery_to q1) (squery_to q2)
  end

with sspec_to (sp : sspec T1 relname) {struct sp} : sspec T2 relname :=
  match sp with
  | Select sq s lf w g h => 
    @Select T2 relname sq 
           (match s with 
            | S_Star _ _ => S_Star T2 relname
            | S_List l => @S_List T2 relname (map sitem_to l)
            end)
           (map sfrom_to lf) (scond_to w) 
           (match g with G_Fine _ _ => G_Fine T2 relname | G_By l => @G_By T2 relname (map sexpr_to l) end)
           (scond_to h)
  end

with sitem_to (x : sitem T1 relname) {struct x} : sitem T2 relname :=
  match x with S_As e a => @S_As T2 relname (sexpr_to e) a end

with sfrom_to (f : sfrom T1 relname) {struct f} : sfrom T2 relname :=
  match f with
  | Fr_Query q r => @Fr_Query T2 relname (squery_to q) (ren_to r)
  | Fr_Join jt lat f1 f2 c => @Fr_Join T2 relname jt lat (sfrom_to f1) (sfrom_to f2) (scond_to c)
  end

with sorder_to (o : sorder T1 relname) {struct o} : sorder T2 relname :=
  match o with O_By e d n => @O_By T2 relname (sexpr_to e) d n end

with swindow_to (w : swindow T1 relname) {struct w} : swindow T2 relname :=
  match w with
  | W_As f lp lo a => @W_As T2 relname (swfun_to f) (map sexpr_to lp) (map sorder_to lo) a
  end

with swfun_to (f : swfun T1 relname) {struct f} : swfun T2 relname :=
  match f with
  | W_Agg ag sq e fr => @W_Agg T2 relname ag sq (sexpr_to e) fr
  | W_Row_Number _ _ => W_Row_Number T2 relname
  | W_Rank _ _ => W_Rank T2 relname
  | W_Dense_Rank _ _ => W_Dense_Rank T2 relname
  | W_Ntile _ _ n => W_Ntile T2 relname n
  | W_Lag e n d => @W_Lag T2 relname (sexpr_to e) n (sexpr_to d)
  | W_Lead e n d => @W_Lead T2 relname (sexpr_to e) n (sexpr_to d)
  | W_First_Value e fr => @W_First_Value T2 relname (sexpr_to e) fr
  | W_Last_Value e fr => @W_Last_Value T2 relname (sexpr_to e) fr
  | W_Nth_Value e n fr => @W_Nth_Value T2 relname (sexpr_to e) n fr
  end.

End Transport.

Definition to_dialect (d : vsem) {relname : Type} (q : squery TNull relname) : squery (TD d) relname :=
  squery_to d relname q.

