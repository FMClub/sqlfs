(** * The static type of every expression and of the columns of every query (TODO 6.2)

    [typeof_e fam sc e] is the type which the engines of the family [fam] give to the expression [e] in the
    scope [sc] (the columns of the enclosing blocks, the innermost first), [typeof_q] the types of the
    columns of a query (the columns of a derived table are those of its query, a [WITH] relation has the
    types of its definition). [None] is a type error of the engine (the branches of a [CASE], [COALESCE] or
    set operation which cannot be matched, [common_type] of [Typing.v]).
    - constants: [stype_of_value]; columns: their declared types; functions: [fun_type] (arithmetic by the
      preferred numeric type, the division of integers is an integer in PostgreSQL and a decimal in the
      MySQL family, comparisons are booleans, and integers in the MySQL family, the string functions give
      text, [length] an integer, casts their target, [ROUND], [CEIL], [FLOOR] of an integer a double precision
      in PostgreSQL); aggregates: [agg_type] ([count] an integer, [sum] of integers an integer in PostgreSQL
      and a decimal in the MySQL family, [avg] of integers a decimal, [min] and [max] the type of their
      argument); window functions: the ranks are integers, [percent_rank] and [cume_dist] double precision;
    - SQLite has no static types: every expression which is not a constant or a column is [ST_Unknown];
    - a function which the tables do not know is [ST_Unknown].
    The results are those of PostgreSQL 16 ([pg_typeof]) and MariaDB 10.11 ([CREATE TABLE ... AS SELECT]),
    checked on live engines ([Test_TypeOf.v]). [typeof_sort]: the columns which [typeof_q] gives are the
    sort of the query. *)
Require Import List String Bool.
Require Import OrderedSet FiniteSet FlatData SqlFull SqlInduction Values GenericInstance Typing.
Import ListNotations.
Open Scope string_scope.

Section Sec.

Hypothesis rel : Type.
Hypothesis ORN : Oset.Rcd rel.
Variable fam : type_family.

Notation sexpr := (sexpr TNull rel).
Notation scond := (scond TNull rel).
Notation squery := (squery TNull rel).
Notation sspec := (sspec TNull rel).
Notation sfrom := (sfrom TNull rel).

Definition cols := list (attribute * stype).

Fixpoint assoc_type (a : attribute) (l : cols) : option stype :=
  match l with
  | nil => None
  | (b, t) :: l => if Oset.eq_bool OAN a b then Some t else assoc_type a l
  end.

(** a column, from the innermost block which has it *)
Fixpoint col_type (a : attribute) (sc : list cols) : stype :=
  match sc with
  | nil => ST_Unknown
  | c :: sc => match assoc_type a c with Some t => t | None => col_type a sc end
  end.

Definition sqlite := match fam with TF_SQLite => true | _ => false end.
Definition mysql := match fam with TF_MySQL => true | _ => false end.
Definition pg := match fam with TF_PostgreSQL => true | _ => false end.

Definition numeric (t : stype) := match t with ST_Int | ST_Decimal | ST_Float | ST_Bool => true | _ => false end.

(** the numeric type of an arithmetic operation: the wider of the operands ([ST_Null] is neutral) *)
Definition num_join (l : list stype) : stype :=
  fold_left (fun acc t => match acc, t with
                          | ST_Null, t => t
                          | acc, ST_Null => acc
                          | ST_Float, _ | _, ST_Float => ST_Float
                          | ST_Decimal, _ | _, ST_Decimal => ST_Decimal
                          | ST_Unknown, _ | _, ST_Unknown => if pg then ST_Int else ST_Unknown
                          | _, _ => ST_Int
                          end) l ST_Null.

Definition bool_type := if mysql then ST_Int else ST_Bool.

Definition mem_s (s : string) (l : list string) := existsb (String.eqb s) l.

Definition fun_type (f : string) (args : list stype) : option stype :=
  if mem_s f ["+"; "-"; "*"; "%"; "mod"; "neg"; "abs"] then Some (num_join args)
  else if String.eqb f "/" then
    Some (match num_join args with
          | ST_Int | ST_Bool => if pg then ST_Int else ST_Decimal
          | t => t end)
  else if mem_s f ["round"; "ceil"; "ceiling"; "floor"; "trunc"; "truncate"] then
    Some (match num_join (firstn 1 args) with
          | ST_Int | ST_Bool => if pg then ST_Float else ST_Int
          | ST_Decimal => if mysql && negb (String.eqb f "round") && negb (String.eqb f "truncate") then ST_Int else ST_Decimal
          | t => t end)
  else if mem_s f ["="; "<>"; "!="; "<"; "<="; ">"; ">="; "<=>"; "like"; "not like"; "is null"; "is not null";
                   "between"; "not between"; "in"; "not in"; "and"; "or"; "not"; "regexp"; "is distinct from";
                   "is not distinct from"] then Some bool_type
  else if mem_s f ["upper"; "lower"; "ucase"; "lcase"; "concat"; "||"; "substr"; "substring"; "trim"; "ltrim";
                   "rtrim"; "btrim"; "replace"; "lpad"; "rpad"; "left"; "right"; "repeat"; "reverse"; "md5";
                   "initcap"; "concat_ws"; "cast_string"; "cast_text"; "cast_char"; "cast_varchar"; "to_char";
                   "version"; "database"; "user"; "current_user"] then Some ST_Text
  else if mem_s f ["length"; "char_length"; "character_length"; "octet_length"; "strpos"; "position"; "instr";
                   "locate"; "ascii"; "cast_int"; "cast_signed"; "cast_integer"; "cast_bigint"; "cast_smallint";
                   "cast_unsigned"; "div"; "sign"] then
    Some (if String.eqb f "sign" && pg then num_join args else ST_Int)
  else if mem_s f ["cast_decimal"; "cast_numeric"] then Some ST_Decimal
  else if mem_s f ["cast_double"; "cast_float"; "cast_real"; "cast_float4"; "cast_float8"; "sqrt"; "exp"; "ln"; "log"; "power"; "pow"; "sin";
                   "cos"; "tan"; "pi"; "random"; "rand"] then Some ST_Float
  else if mem_s f ["cast_date"; "current_date"; "curdate"] then Some ST_Date
  else if mem_s f ["cast_datetime"; "cast_timestamp"; "cast_timestamptz"; "now"; "current_timestamp"; "localtimestamp"] then Some ST_Timestamp
  else if mem_s f ["cast_time"; "current_time"; "curtime"] then Some ST_Time
  else if mem_s f ["cast_bool"; "cast_boolean"] then Some bool_type
  else if mem_s f ["cast_json"; "cast_jsonb"] then Some ST_Json
  else if String.eqb f "cast_interval" then Some ST_Interval
  else if mem_s f ["coalesce"; "ifnull"; "nvl"; "greatest"; "least"] then common_type_of fam args
  else if String.eqb f "nullif" then Some (match args with t :: _ => t | nil => ST_Null end)
  else Some ST_Unknown.

Definition agg_type (a : string) (arg : stype) : stype :=
  let a := if String.prefix "distinct " a then String.substring 9 (String.length a - 9) a else a in
  if String.prefix "count" a then ST_Int
  else if String.eqb a "sum" then
    match arg with
    | ST_Int | ST_Bool => if pg then ST_Int else ST_Decimal
    | ST_Null | ST_Unknown => if pg then ST_Int else ST_Decimal
    | t => t end
  else if mem_s a ["avg"; "stddev"; "stddev_pop"; "stddev_samp"; "variance"; "var_pop"; "var_samp"] then
    match arg with
    | ST_Float => ST_Float
    | _ => if mysql && negb (String.eqb a "avg") then ST_Float else ST_Decimal end
  else if mem_s a ["min"; "max"; "any_value"] then arg
  else if mem_s a ["string_agg"; "group_concat"; "listagg"] then ST_Text
  else if mem_s a ["bool_and"; "bool_or"; "every"] then bool_type
  else ST_Unknown.

Definition sym_name (f : Values.symbol NullValues.value) :=
  match f with Values.Symbol _ s => s | Values.CstVal _ _ => "" end.
Definition agg_name (a : Values.aggregate) := match a with Values.Aggregate s => s end.

Definition lit (v : NullValues.value) := stype_of_value pg v.

Fixpoint typeof_e (ce : list (rel * cols)) (sc : list cols) (e : sexpr) {struct e} : option stype :=
  let sq_ty (t : stype) := if sqlite then ST_Unknown else t in
  match e with
  | E_Const _ _ v => Some (lit v)
  | E_Col _ _ a => Some (col_type a sc)
  | E_Fun f l =>
    match f with
    | Values.CstVal _ v => Some (lit v)
    | _ =>
      let ts := (fix go (l : list sexpr) : option (list stype) :=
                   match l with
                   | nil => Some nil
                   | x :: r => match typeof_e ce sc x, go r with Some t, Some ts => Some (t :: ts) | _, _ => None end
                   end) l in
      match ts with
      | Some ts => option_map sq_ty (fun_type (sym_name f) ts)
      | None => None
      end
    end
  | E_Agg ag _ x _ | E_AggX ag _ x _ _ _ =>
    match typeof_e ce sc x with Some t => Some (sq_ty (agg_type (agg_name ag) t)) | None => None end
  | E_Case c e1 e2 =>
    match typeof_c ce sc c, typeof_e ce sc e1, typeof_e ce sc e2 with
    | true, Some t1, Some t2 => if sqlite then Some ST_Unknown else common_type_of fam (t1 :: t2 :: nil)
    | _, _, _ => None
    end
  | E_Cond c => if typeof_c ce sc c then Some (sq_ty bool_type) else None
  | E_Sub q => match typeof_q ce sc q with Some ((_, t) :: nil) => Some t | Some _ => Some ST_Unknown | None => None end
  | E_Grouping _ => Some ST_Int
  end

(** a condition is well typed *)
with typeof_c (ce : list (rel * cols)) (sc : list cols) (c : scond) {struct c} : bool :=
  match c with
  | C_Conj _ c1 c2 => typeof_c ce sc c1 && typeof_c ce sc c2
  | C_Not c => typeof_c ce sc c
  | C_True _ _ => true
  | C_Pred _ l | C_Quant _ _ l _ _ | C_In l _ _ =>
    (fix go (l : list sexpr) : bool :=
       match l with nil => true | x :: r => match typeof_e ce sc x with Some _ => go r | None => false end end) l
  | C_Expr e => match typeof_e ce sc e with Some _ => true | None => false end
  | C_Exists q => match typeof_q ce sc q with Some _ => true | None => false end
  end

with typeof_q (ce : list (rel * cols)) (sc : list cols) (q : squery) {struct q} : option cols :=
  match q with
  | SQ_Table _ r => Some (match Oset.find ORN r ce with Some c => c | None => nil end)
  | SQ_Set _ _ q1 q2 =>
    match typeof_q ce sc q1, typeof_q ce sc q2 with
    | Some c1, Some c2 =>
      (fix go (c1 : cols) : option cols :=
         match c1 with
         | nil => Some nil
         | (a, t1) :: r =>
           match (if sqlite then Some ST_Unknown
                  else common_type_of fam (t1 :: match assoc_type a c2 with Some t2 => t2 | None => ST_Null end :: nil)),
                 go r with
           | Some t, Some r' => Some ((a, t) :: r')
           | _, _ => None
           end
         end) c1
    | _, _ => None
    end
  | SQ_Select sp => typeof_s ce sc sp
  | SQ_Order q _ _ _ | SQ_Fetch q _ _ _ _ _ => typeof_q ce sc q
  | SQ_Window q lw =>
    match typeof_q ce sc q with
    | Some c =>
      Some (app c (map (fun w => match w with
                               | W_As f _ _ a =>
                                 (a, (fix wt (f : swfun TNull rel) : stype :=
                                        match f with
                                        | W_Row_Number _ _ | W_Rank _ _ | W_Dense_Rank _ _ | W_Ntile _ _ _ => ST_Int
                                        | W_Percent_Rank _ _ | W_Cume_Dist _ _ => ST_Float
                                        | W_Agg ag _ x _ =>
                                          match typeof_e ce (c :: sc) x with
                                          | Some t => agg_type (agg_name ag) t | None => ST_Unknown end
                                        | W_Lag x _ _ | W_Lead x _ _ | W_First_Value x _ | W_Last_Value x _
                                        | W_Nth_Value x _ _ =>
                                          match typeof_e ce (c :: sc) x with Some t => t | None => ST_Unknown end
                                        | W_Opts f' _ _ => wt f'
                                        end) f)
                               end) lw))
    | None => None
    end
  | SQ_With r q1 q2 =>
    match typeof_q ce sc q1 with Some c1 => typeof_q ((r, c1) :: ce) sc q2 | None => None end
  | SQ_WithRec _ r q1 q2 q3 =>
    match typeof_q ce sc q1 with
    | Some c1 => match typeof_q ((r, c1) :: ce) sc q2 with
                 | Some _ => typeof_q ((r, c1) :: ce) sc q3
                 | None => None end
    | None => None
    end
  end

with typeof_s (ce : list (rel * cols)) (sc : list cols) (sp : sspec) {struct sp} : option cols :=
  match sp with
  | Select _ s lf w g h =>
    match (fix go (lf : list sfrom) : option cols :=
             match lf with
             | nil => Some nil
             | f :: r => match typeof_f ce sc f, go r with Some c, Some c' => Some (app c c') | _, _ => None end
             end) lf with
    | Some fc =>
      if typeof_c ce (fc :: sc) w && typeof_c ce (fc :: sc) h then
        match s with
        | S_Star _ _ => Some fc
        | S_List l =>
          (fix go (l : list (sitem TNull rel)) : option cols :=
             match l with
             | nil => Some nil
             | S_As e a :: r => match typeof_e ce (fc :: sc) e, go r with
                                | Some t, Some r' => Some ((a, t) :: r')
                                | _, _ => None
                                end
             end) l
        end
      else None
    | None => None
    end
  end

with typeof_f (ce : list (rel * cols)) (sc : list cols) (f : sfrom) {struct f} : option cols :=
  match f with
  | Fr_Query q (Ren_Star _) => typeof_q ce sc q
  | Fr_Query q (Ren_List _ l) =>
    match typeof_q ce sc q with
    | Some c => Some (map (fun p => (snd p, match assoc_type (fst p) c with Some t => t | None => ST_Unknown end)) l)
    | None => None
    end
  | Fr_Join _ lat f1 f2 _ =>
    match typeof_f ce sc f1 with
    | Some c1 => match typeof_f ce (if lat then c1 :: sc else sc) f2 with Some c2 => Some (app c1 c2) | None => None end
    | None => None
    end
  | Fr_Fun _ _ _ atts => Some (map (fun a => (a, ST_Unknown)) atts)
  end.

End Sec.

(** * The columns of a query are its sort *)
Section Sort.

Hypothesis rel : Type.
Hypothesis ORN : Oset.Rcd rel.
Variable fam : type_family.
Hypothesis basesort : rel -> Fset.set (Tuple.A TNull).

Notation squery := (squery TNull rel).
Notation memA a s := (Fset.mem (Tuple.A TNull) a s).
Notation keys c := (Fset.mk_set (Tuple.A TNull) (map (@fst _ _) c)).

Definition tsort (tce : list (rel * cols)) r := match Oset.find ORN r tce with Some c => c | None => nil end.
Definition esort (ce : cte_env TNull rel) r := match Oset.find ORN r ce with Some (s, _) => s | None => basesort r end.

(** the types of the relations have the attributes of their sorts *)
Definition tce_ok tce ce := forall r a, memA a (keys (tsort tce r)) = memA a (esort ce r).

Lemma tce_ok_cons : forall tce ce r c s l, tce_ok tce ce -> (forall a, memA a (keys c) = memA a s) ->
  tce_ok ((r, c) :: tce) ((r, (s, l)) :: ce).
Proof.
intros tce ce r c s l H E r0 a; unfold tsort, esort, Oset.find; cbn [Mem.find].
destruct (Oset.eq_bool ORN r0 r); [apply E | apply H].
Qed.

Lemma keys_app : forall (c1 c2 : cols) a, memA a (keys (app c1 c2)) = memA a (keys c1) || memA a (keys c2).
Proof. intros; rewrite map_app; apply Fset.mem_mk_set_app. Qed.

Notation Pq q := (forall tce ce sc c, tce_ok tce ce -> typeof_q rel ORN fam tce sc q = Some c ->
                    forall a, memA a (keys c) = memA a (squery_sort ORN basesort ce q)).
Notation Ps sp := (forall tce ce sc c, tce_ok tce ce -> typeof_s rel ORN fam tce sc sp = Some c ->
                    forall a, memA a (keys c) = memA a (sspec_sort ORN basesort ce sp)).
Notation Pf f := (forall tce ce sc c, tce_ok tce ce -> typeof_f rel ORN fam tce sc f = Some c ->
                    forall a, memA a (keys c) = memA a (sfrom_sort ORN basesort ce f)).

Ltac unft := cbn [typeof_q typeof_s typeof_f squery_sort sspec_sort sfrom_sort] in *;
  fold (typeof_e rel ORN fam) (typeof_c rel ORN fam) (typeof_q rel ORN fam) (typeof_s rel ORN fam) (typeof_f rel ORN fam)
       (@squery_sort TNull rel ORN basesort) (@sspec_sort TNull rel ORN basesort) (@sfrom_sort TNull rel ORN basesort) in *.

Theorem typeof_sort : forall q, Pq q.
Proof.
apply (ind_q TNull rel (fun _ => True) (fun _ => True) (fun q => Pq q) (fun sp => Ps sp) (fun f => Pf f));
  intros; try exact I; unft.
(* SQ_Table *)
- injection H0; intros <-; apply H.
(* SQ_Set *)
- destruct (typeof_q rel ORN fam tce sc q1) as [c1 | ] eqn:E1; [ | discriminate].
  destruct (typeof_q rel ORN fam tce sc q2) as [c2 | ] eqn:E2; [ | discriminate].
  rewrite <- (H tce ce sc c1 H1 E1 a); clear E1 E2; revert c H2; induction c1 as [ | [b t1] r IH]; intros c Hc.
  + injection Hc; intros <-; reflexivity.
  + match type of Hc with (match ?X with _ => _ end) = _ => destruct X as [t | ] end; [ | discriminate].
    match type of Hc with (match ?X with _ => _ end) = _ => destruct X as [r' | ] eqn:Er end; [ | discriminate].
    injection Hc; intros <-; specialize (IH r' eq_refl); rewrite !Fset.mem_mk_set in *; cbn [map fst]; rewrite !(Oset.mem_bool_unfold _ a (_ :: _)), IH; reflexivity.
(* SQ_Select *)
- exact (H tce ce sc c H0 H1 a).
(* SQ_Order, SQ_Fetch *)
- exact (H tce ce sc c H2 H3 a).
- exact (H tce ce sc c H2 H3 a).
(* SQ_Window *)
- destruct (typeof_q rel ORN fam tce sc q) as [c0 | ] eqn:E; [ | discriminate].
  injection H2; intros <-; rewrite keys_app, Fset.mem_union, (H tce ce sc c0 H1 E a), map_map, !Fset.mem_mk_set.
  f_equal; f_equal; apply map_ext; intros [f lp lo a']; reflexivity.
(* SQ_With *)
- destruct (typeof_q rel ORN fam tce sc q1) as [c1 | ] eqn:E; [ | discriminate].
  apply (H0 ((r, c1) :: tce) ((r, (squery_sort ORN basesort ce q1, nil)) :: ce) sc c); [ | exact H2].
  apply tce_ok_cons; [exact H1 | exact (H tce ce sc c1 H1 E)].
(* SQ_WithRec *)
- destruct (typeof_q rel ORN fam tce sc q1) as [c1 | ] eqn:E; [ | discriminate].
  destruct (typeof_q rel ORN fam ((r, c1) :: tce) sc q2) as [c2 | ]; [ | discriminate].
  apply (H1 ((r, c1) :: tce) ((r, (squery_sort ORN basesort ce q1, nil)) :: ce) sc c); [ | exact H3].
  apply tce_ok_cons; [exact H2 | exact (H tce ce sc c1 H2 E)].
(* Select *)
- match type of H5 with (match ?X with _ => _ end) = _ => destruct X as [fc | ] eqn:Ef end; [ | discriminate].
  destruct (_ && _); [ | discriminate].
  destruct s as [ | l].
  + injection H5; intros <-; clear H5 H; revert fc Ef; induction lf as [ | f lf IH]; intros fc Ef.
    * injection Ef; intros <-; rewrite Fset.Union_unfold; reflexivity.
    * match type of Ef with (match ?X with _ => _ end) = _ => destruct X as [c1 | ] eqn:E1 end; [ | discriminate].
      match type of Ef with (match ?X with _ => _ end) = _ => destruct X as [c2 | ] eqn:E2 end; [ | discriminate].
      injection Ef; intros <-; rewrite keys_app.
      change (map (sfrom_sort ORN basesort ce) (f :: lf)) with (sfrom_sort ORN basesort ce f :: map (sfrom_sort ORN basesort ce) lf).
      rewrite (Fset.Union_unfold _ (sfrom_sort ORN basesort ce f :: _)), Fset.mem_union.
      rewrite (H0 f (or_introl eq_refl) tce ce sc c1 H4 E1 a), (IH (fun f' Hf' => H0 f' (or_intror Hf')) c2 eq_refl).
      reflexivity.
  + clear Ef; revert c H5; induction l as [ | [e a'] l IH]; intros c Hc.
    * injection Hc; intros <-; reflexivity.
    * match type of Hc with (match ?X with _ => _ end) = _ => destruct X as [t | ] end; [ | discriminate].
      match type of Hc with (match ?X with _ => _ end) = _ => destruct X as [r' | ] eqn:Er end; [ | discriminate].
      injection Hc; intros <-; specialize (IH (fun _ _ _ => I) r' eq_refl); cbn [sspec_sort] in *; rewrite !Fset.mem_mk_set in *; cbn [map fst]; rewrite !(Oset.mem_bool_unfold _ a (_ :: _)).
      rewrite IH; reflexivity.
(* Fr_Query *)
- destruct rho as [ | l]; cbn [sfrom_sort]; fold (@squery_sort TNull rel ORN basesort).
  + exact (H tce ce sc c H0 H1 a).
  + destruct (typeof_q rel ORN fam tce sc q); [ | discriminate].
    injection H1; intros <-; rewrite map_map; reflexivity.
(* Fr_Join *)
- destruct (typeof_f rel ORN fam tce sc f1) as [c1 | ] eqn:E1; [ | discriminate].
  destruct (typeof_f rel ORN fam tce (if lat then c1 :: sc else sc) f2) as [c2 | ] eqn:E2; [ | discriminate].
  injection H3; intros <-; rewrite keys_app, Fset.mem_union, (H tce ce sc c1 H2 E1 a), (H0 tce ce _ c2 H2 E2 a).
  reflexivity.
(* Fr_Fun *)
- injection H1; intros <-; rewrite map_map, map_id; reflexivity.
Qed.

End Sort.
