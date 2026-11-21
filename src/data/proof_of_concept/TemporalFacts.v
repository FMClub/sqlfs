(** * The calendar conversions are inverse of each other

    [civil_from_days] and [days_from_civil] ([Temporal.v]) are the conversions between a number of days and a date
    of the proleptic Gregorian calendar. Both are periodic: 400 years are 146097 days ([civil_shift],
    [days_shift]). So the round trip holds for every day as soon as it holds for the days of one period, which is
    checked by computation ([round_trip_period]): [civil_round_trip]. The dates which [civil_from_days] returns
    are valid ([civil_valid]). (An error in the division for the negative years, found by the audit of iteration
    7, would have made this proof fail.) *)
Require Import List Bool ZArith Lia.
Require Import Temporal.
Open Scope Z_scope.

Definition round_trip (z : Z) : Prop :=
  let '(y, m, d) := civil_from_days z in days_from_civil y m d = z.

Lemma civil_shift : forall z,
  civil_from_days (z + 146097) = let '(y, m, d) := civil_from_days z in (y + 400, m, d).
Proof.
intro z; unfold civil_from_days.
replace (z + 146097 + 719468) with (z + 719468 + 1 * 146097) by ring.
rewrite Z.div_add by discriminate.
replace (z + 719468 + 1 * 146097 - ((z + 719468) / 146097 + 1) * 146097)
  with (z + 719468 - (z + 719468) / 146097 * 146097) by ring.
set (doe := z + 719468 - (z + 719468) / 146097 * 146097).
set (yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365).
set (doy := doe - (365 * yoe + yoe / 4 - yoe / 100)).
set (mp := (5 * doy + 2) / 153).
destruct ((if mp <? 10 then mp + 3 else mp - 9) <=? 2); f_equal; f_equal; ring.
Qed.

Lemma days_shift : forall y m d, days_from_civil (y + 400) m d = days_from_civil y m d + 146097.
Proof.
intros y m d; unfold days_from_civil.
replace (if m <=? 2 then y + 400 - 1 else y + 400) with ((if m <=? 2 then y - 1 else y) + 1 * 400)
  by (destruct (m <=? 2); ring).
set (y0 := if m <=? 2 then y - 1 else y).
rewrite Z.div_add by discriminate.
replace (y0 + 1 * 400 - (y0 / 400 + 1) * 400) with (y0 - y0 / 400 * 400) by ring.
ring.
Qed.

Lemma round_trip_shift : forall z, round_trip z <-> round_trip (z + 146097).
Proof.
intro z; unfold round_trip; rewrite civil_shift.
destruct (civil_from_days z) as [[y m] d]; rewrite days_shift; lia.
Qed.

(** one period, by computation: the days [z], [z + 1], ..., [n] of them *)
Definition day_ok (z : Z) : bool :=
  let '(y, m, d) := civil_from_days z in Z.eqb (days_from_civil y m d) z && valid_date y m d.

Fixpoint days_ok (n : nat) (z : Z) : bool :=
  match n with
  | O => true
  | S n' => day_ok z && days_ok n' (z + 1)
  end.

Lemma days_ok_spec : forall n z0, days_ok n z0 = true -> forall z, z0 <= z < z0 + Z.of_nat n -> day_ok z = true.
Proof.
intro n; induction n as [ | n IH]; intros z0 H z Hz; [simpl in Hz; lia | ].
simpl in H; rewrite andb_true_iff in H; destruct H as [H1 H2].
destruct (Z.eq_dec z z0) as [E | N]; [subst z; exact H1 | ].
apply (IH (z0 + 1) H2); rewrite Nat2Z.inj_succ in Hz; lia.
Qed.

Definition period : nat := Z.to_nat 146097.

Lemma period_ok : days_ok period 0 = true.
Proof. vm_compute; reflexivity. Qed.

Lemma round_trip_period : forall z, 0 <= z < 146097 -> round_trip z /\ (let '(y, m, d) := civil_from_days z in valid_date y m d = true).
Proof.
intros z Hz; assert (K := days_ok_spec period 0 period_ok z).
unfold period in K; rewrite Z2Nat.id in K by discriminate; specialize (K Hz).
unfold day_ok in K; unfold round_trip.
destruct (civil_from_days z) as [[y m] d]; rewrite andb_true_iff, Z.eqb_eq in K; exact K.
Qed.

Lemma round_trip_mult : forall r k, round_trip r -> round_trip (r + k * 146097).
Proof.
intros r k H; induction k using Z.peano_ind.
- rewrite Z.add_0_r; exact H.
- replace (r + Z.succ k * 146097) with (r + k * 146097 + 146097) by (unfold Z.succ; ring).
  apply (proj1 (round_trip_shift (r + k * 146097))); exact IHk.
- apply (proj2 (round_trip_shift (r + Z.pred k * 146097))).
  replace (r + Z.pred k * 146097 + 146097) with (r + k * 146097) by (unfold Z.pred; ring); exact IHk.
Qed.

(** the date of a day is the date whose day it is *)
Theorem civil_round_trip : forall z, let '(y, m, d) := civil_from_days z in days_from_civil y m d = z.
Proof.
intro z; change (round_trip z).
replace z with (z mod 146097 + (z / 146097) * 146097) by (rewrite (Z.div_mod z 146097) at 3 by discriminate; ring).
apply round_trip_mult, round_trip_period, Z.mod_pos_bound; reflexivity.
Qed.

(** the dates of the days are valid *)
Lemma valid_shift : forall y m d, valid_date (y + 400) m d = valid_date y m d.
Proof.
intros y m d; unfold valid_date, days_in_month, is_leap.
replace ((y + 400) mod 4) with (y mod 4) by (replace (y + 400) with (y + 100 * 4) by ring; rewrite Z.mod_add by discriminate; reflexivity).
replace ((y + 400) mod 100) with (y mod 100) by (replace (y + 400) with (y + 4 * 100) by ring; rewrite Z.mod_add by discriminate; reflexivity).
replace ((y + 400) mod 400) with (y mod 400) by (replace (y + 400) with (y + 1 * 400) by ring; rewrite Z.mod_add by discriminate; reflexivity).
reflexivity.
Qed.

Theorem civil_valid : forall z, let '(y, m, d) := civil_from_days z in valid_date y m d = true.
Proof.
intro z.
assert (S : forall r k, (let '(y, m, d) := civil_from_days r in valid_date y m d = true) ->
                        let '(y, m, d) := civil_from_days (r + k * 146097) in valid_date y m d = true).
{ intros r k H; induction k using Z.peano_ind.
  - rewrite Z.add_0_r; exact H.
  - replace (r + Z.succ k * 146097) with (r + k * 146097 + 146097) by (unfold Z.succ; ring); rewrite civil_shift.
    destruct (civil_from_days (r + k * 146097)) as [[y m] d]; rewrite valid_shift; exact IHk.
  - replace (r + k * 146097) with (r + Z.pred k * 146097 + 146097) in IHk by (unfold Z.pred; ring); rewrite civil_shift in IHk.
    destruct (civil_from_days (r + Z.pred k * 146097)) as [[y m] d]; rewrite valid_shift in IHk; exact IHk. }
replace z with (z mod 146097 + (z / 146097) * 146097) by (rewrite (Z.div_mod z 146097) at 3 by discriminate; ring).
apply S, round_trip_period, Z.mod_pos_bound; reflexivity.
Qed.

(** * The converse: the day of a valid date is the day whose date it is *)

Definition date_ok (y m d : Z) : bool :=
  negb (valid_date y m d) ||
  (let '(y', m', d') := civil_from_days (days_from_civil y m d) in Z.eqb y' y && Z.eqb m' m && Z.eqb d' d).

Definition year_ok (y : Z) : bool :=
  forallb (fun m => forallb (fun d => date_ok y (Z.of_nat m) (Z.of_nat d)) (seq 1 31)) (seq 1 12).

Fixpoint years_ok (n : nat) (y : Z) : bool :=
  match n with
  | O => true
  | S n' => year_ok y && years_ok n' (y + 1)
  end.

Lemma years_ok_spec : forall n y0, years_ok n y0 = true -> forall y, y0 <= y < y0 + Z.of_nat n -> year_ok y = true.
Proof.
intro n; induction n as [ | n IH]; intros y0 H y Hy; [simpl in Hy; lia | ].
simpl in H; rewrite andb_true_iff in H; destruct H as [H1 H2].
destruct (Z.eq_dec y y0) as [E | N]; [subst y; exact H1 | ].
apply (IH (y0 + 1) H2); rewrite Nat2Z.inj_succ in Hy; lia.
Qed.

Lemma years_period_ok : years_ok 400 0 = true.
Proof. vm_compute; reflexivity. Qed.

Lemma valid_range : forall y m d, valid_date y m d = true -> 1 <= m <= 12 /\ 1 <= d <= 31.
Proof.
intros y m d H; unfold valid_date in H; rewrite !andb_true_iff, !Z.leb_le in H.
destruct H as [[[H1 H2] H3] H4]; split; [lia | split; [exact H3 | ]].
assert (K : days_in_month y m <= 31).
{ assert (E : m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6 \/ m = 7 \/ m = 8 \/ m = 9 \/ m = 10 \/ m = 11 \/ m = 12) by lia.
  repeat (destruct E as [E | E]; [subst m; simpl; try (destruct (is_leap y)); lia | ]).
  subst m; simpl; lia. }
lia.
Qed.

Lemma date_period : forall y m d, 0 <= y < 400 -> valid_date y m d = true ->
  civil_from_days (days_from_civil y m d) = (y, m, d).
Proof.
intros y m d Hy Hv; assert (K := years_ok_spec 400 0 years_period_ok y Hy).
destruct (valid_range y m d Hv) as [Hm Hd].
unfold year_ok in K; rewrite forallb_forall in K.
assert (Im : In (Z.to_nat m) (seq 1 12)) by (rewrite in_seq; lia).
specialize (K _ Im); rewrite forallb_forall in K.
assert (Id : In (Z.to_nat d) (seq 1 31)) by (rewrite in_seq; lia).
specialize (K _ Id); rewrite !Z2Nat.id in K by lia.
unfold date_ok in K; rewrite Hv in K; cbn [negb orb] in K.
destruct (civil_from_days (days_from_civil y m d)) as [[y' m'] d'].
rewrite !andb_true_iff, !Z.eqb_eq in K; destruct K as [[E1 E2] E3]; subst; reflexivity.
Qed.

Lemma date_shift : forall y m d k,
  civil_from_days (days_from_civil (y + k * 400) m d) =
  let '(y', m', d') := civil_from_days (days_from_civil y m d) in (y' + k * 400, m', d').
Proof.
intros y m d k; induction k using Z.peano_ind.
- rewrite Z.add_0_r; destruct (civil_from_days (days_from_civil y m d)) as [[y' m'] d']; f_equal; f_equal; ring.
- replace (y + Z.succ k * 400) with (y + k * 400 + 400) by (unfold Z.succ; ring).
  rewrite days_shift, civil_shift, IHk.
  destruct (civil_from_days (days_from_civil y m d)) as [[y' m'] d']; f_equal; f_equal; unfold Z.succ; ring.
- replace (y + k * 400) with (y + Z.pred k * 400 + 400) in IHk by (unfold Z.pred; ring).
  rewrite days_shift, civil_shift in IHk.
  destruct (civil_from_days (days_from_civil (y + Z.pred k * 400) m d)) as [[y1 m1] d1].
  destruct (civil_from_days (days_from_civil y m d)) as [[y' m'] d'].
  inversion IHk; subst; f_equal; f_equal; unfold Z.pred in *; lia.
Qed.

Lemma valid_mult : forall y m d k, valid_date (y + k * 400) m d = valid_date y m d.
Proof.
intros y m d k; induction k using Z.peano_ind.
- rewrite Z.add_0_r; reflexivity.
- replace (y + Z.succ k * 400) with (y + k * 400 + 400) by (unfold Z.succ; ring); rewrite valid_shift; exact IHk.
- rewrite <- IHk; replace (y + k * 400) with (y + Z.pred k * 400 + 400) by (unfold Z.pred; ring).
  rewrite valid_shift; reflexivity.
Qed.

Theorem days_round_trip : forall y m d, valid_date y m d = true ->
  civil_from_days (days_from_civil y m d) = (y, m, d).
Proof.
intros y m d Hv.
assert (E : y = y mod 400 + (y / 400) * 400) by (rewrite (Z.div_mod y 400) at 1 by discriminate; ring).
rewrite E in Hv; rewrite valid_mult in Hv.
rewrite E at 1; rewrite date_shift, (date_period (y mod 400) m d); [ | apply Z.mod_pos_bound; reflexivity | exact Hv].
f_equal; f_equal; symmetry; exact E.
Qed.
