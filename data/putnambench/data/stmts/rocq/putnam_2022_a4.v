(* Statement-only formalization of PutnamBench corpus artifact putnam_2022_a4:
   the expected weighted sum of independent uniform unit-interval random
   variables stopped at the first failure of strict descent. This file contains
   no proof. *)

From Stdlib Require Import Reals List ClassicalDescription.

Set Implicit Arguments.
Local Open Scope R_scope.

Definition set (A : Type) := A -> Prop.

Definition empty_set {A : Type} : set A :=
  fun _ => False.

Definition full_set {A : Type} : set A :=
  fun _ => True.

Definition set_complement {A : Type} (E : set A) : set A :=
  fun x => ~ E x.

Definition set_intersection {A : Type} (E F : set A) : set A :=
  fun x => E x /\ F x.

Definition countable_union {A : Type} (E : nat -> set A) : set A :=
  fun x => exists n : nat, E n x.

Definition preimage {A B : Type} (f : A -> B) (E : set B) : set A :=
  fun x => E (f x).

Definition same_set {A : Type} (E F : set A) : Prop :=
  forall x : A, E x <-> F x.

Definition disjoint_sets {A : Type} (E F : set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition pairwise_disjoint {A : Type} (E : nat -> set A) : Prop :=
  forall i j : nat, i <> j -> disjoint_sets (E i) (E j).

Fixpoint partial_sum (u : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S k => partial_sum u k + u k
  end.

Definition sequence_converges (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Definition series_sum (u : nat -> R) (sum : R) : Prop :=
  sequence_converges (partial_sum u) sum.

Definition absolutely_summable (u : nat -> R) : Prop :=
  exists absolute_sum : R,
    series_sum (fun n : nat => Rabs (u n)) absolute_sum.

Definition real_tsum_value (u : nat -> R) (value : R) : Prop :=
  (absolutely_summable u /\ series_sum u value) \/
  (~ absolutely_summable u /\ value = 0).

Definition sigma_class {A : Type} (C : set (set A)) : Prop :=
  C empty_set /\
  (forall E : set A, C E -> C (set_complement E)) /\
  (forall E : nat -> set A,
      (forall n : nat, C (E n)) ->
      C (countable_union E)).

Definition open_real_set (U : set R) : Prop :=
  forall x : R,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : R, Rabs (y - x) < epsilon -> U y.

Definition borel_set (E : set R) : Prop :=
  forall C : set (set R),
    sigma_class C ->
    (forall U : set R, open_real_set U -> C U) ->
    C E.

Record probability_space (A : Type) := {
  ps_measurable : set A -> Prop;
  ps_measurable_empty : ps_measurable empty_set;
  ps_measurable_complement :
    forall E : set A,
      ps_measurable E ->
      ps_measurable (set_complement E);
  ps_measurable_countable_union :
    forall E : nat -> set A,
      (forall n : nat, ps_measurable (E n)) ->
      ps_measurable (countable_union E);
  ps_measure : set A -> R;
  ps_measure_extensional :
    forall E F : set A,
      same_set E F ->
      ps_measure E = ps_measure F;
  ps_measure_nonnegative :
    forall E : set A,
      ps_measurable E ->
      0 <= ps_measure E;
  ps_measure_empty : ps_measure empty_set = 0;
  ps_measure_total : ps_measure full_set = 1;
  ps_measure_countable_additive :
    forall E : nat -> set A,
      (forall n : nat, ps_measurable (E n)) ->
      pairwise_disjoint E ->
      series_sum
        (fun n : nat => ps_measure (E n))
        (ps_measure (countable_union E))
}.

Arguments ps_measurable {A} _ _.
Arguments ps_measure {A} _ _.

Definition measurable_real_function {A : Type}
    (measurable : set A -> Prop) (f : A -> R) : Prop :=
  forall B : set R,
    borel_set B ->
    measurable (preimage f B).

Definition random_variable {A : Type}
    (P : probability_space A) (X : A -> R) : Prop :=
  measurable_real_function (ps_measurable P) X.

Definition uniform_on_unit_interval {A : Type}
    (P : probability_space A) (X : A -> R) : Prop :=
  random_variable P X /\
  forall t : R,
    (t < 0 -> ps_measure P (fun omega : A => X omega <= t) = 0) /\
    (0 <= t <= 1 ->
      ps_measure P (fun omega : A => X omega <= t) = t) /\
    (1 < t -> ps_measure P (fun omega : A => X omega <= t) = 1).

Fixpoint finite_intersection {A : Type}
    (X : nat -> A -> R) (indices : list nat)
    (events : nat -> set R) : set A :=
  match indices with
  | nil => full_set
  | i :: rest =>
      set_intersection
        (preimage (X i) (events i))
        (finite_intersection X rest events)
  end.

Fixpoint finite_product (indices : list nat) (f : nat -> R) : R :=
  match indices with
  | nil => 1
  | i :: rest => f i * finite_product rest f
  end.

Definition independent_random_variables {A : Type}
    (P : probability_space A) (X : nat -> A -> R) : Prop :=
  forall (indices : list nat) (events : nat -> set R),
    NoDup indices ->
    (forall i : nat, In i indices -> borel_set (events i)) ->
    ps_measure P (finite_intersection X indices events) =
    finite_product indices
      (fun i : nat => ps_measure P (preimage (X i) (events i))).

Definition finite_partition {A : Type}
    (measurable : set A -> Prop)
    (last : nat) (cells : nat -> set A) : Prop :=
  (forall i : nat, (i <= last)%nat -> measurable (cells i)) /\
  (forall i j : nat,
      (i <= last)%nat ->
      (j <= last)%nat ->
      i <> j ->
      disjoint_sets (cells i) (cells j)) /\
  (forall x : A,
      exists i : nat, (i <= last)%nat /\ cells i x).

Fixpoint finite_sum (last : nat) (f : nat -> R) : R :=
  match last with
  | O => f O
  | S n => finite_sum n f + f (S n)
  end.

Definition simple_integral_below {A : Type}
    (measurable : set A -> Prop) (measure : set A -> R)
    (f : A -> R) (value : R) : Prop :=
  exists (last : nat) (coefficients : nat -> R) (cells : nat -> set A),
    finite_partition measurable last cells /\
    (forall i : nat, (i <= last)%nat -> 0 <= coefficients i) /\
    (forall (x : A) (i : nat),
        (i <= last)%nat ->
        cells i x ->
        coefficients i <= f x) /\
    value =
      finite_sum last
        (fun i : nat => coefficients i * measure (cells i)).

Definition least_upper_bound (values : R -> Prop) (bound : R) : Prop :=
  (forall value : R, values value -> value <= bound) /\
  (forall upper : R,
      (forall value : R, values value -> value <= upper) ->
      bound <= upper).

Definition nonnegative_lebesgue_integral {A : Type}
    (measurable : set A -> Prop) (measure : set A -> R)
    (f : A -> R) (value : R) : Prop :=
  least_upper_bound
    (simple_integral_below measurable measure f)
    value.

Definition positive_part (x : R) : R :=
  Rmax x 0.

Definition negative_part (x : R) : R :=
  Rmax (- x) 0.

Definition has_finite_lebesgue_integral {A : Type}
    (measurable : set A -> Prop) (measure : set A -> R)
    (f : A -> R) (value : R) : Prop :=
  measurable_real_function measurable f /\
  exists positive_integral negative_integral : R,
    nonnegative_lebesgue_integral measurable measure
      (fun x : A => positive_part (f x)) positive_integral /\
    nonnegative_lebesgue_integral measurable measure
      (fun x : A => negative_part (f x)) negative_integral /\
    value = positive_integral - negative_integral.

Definition almost_everywhere {A : Type}
    (P : probability_space A) (property : A -> Prop) : Prop :=
  exists null_event : set A,
    ps_measurable P null_event /\
    ps_measure P null_event = 0 /\
    forall x : A, ~ null_event x -> property x.

Definition has_finite_lebesgue_integral_ae {A : Type}
    (P : probability_space A) (f : A -> R) (value : R) : Prop :=
  exists measurable_version : A -> R,
    almost_everywhere P
      (fun x : A => f x = measurable_version x) /\
    has_finite_lebesgue_integral
      (ps_measurable P) (ps_measure P) measurable_version value.

Definition lebesgue_integral_value {A : Type}
    (P : probability_space A) (f : A -> R) (value : R) : Prop :=
  has_finite_lebesgue_integral_ae P f value \/
  ((forall candidate : R,
      ~ has_finite_lebesgue_integral_ae P f candidate) /\
    value = 0).

Definition stopping_index_set {A : Type}
    (X : nat -> A -> R) (K : A -> set nat) : Prop :=
  forall (omega : A) (i : nat),
    K omega i <->
    exists m : nat,
      (i <= m)%nat /\
      forall l : nat,
        (l < m)%nat ->
        X l omega > X (S l) omega.

Definition stopped_term {A : Type}
    (X : nat -> A -> R) (K : A -> set nat)
    (omega : A) (i : nat) : R :=
  if excluded_middle_informative (K omega i)
  then X i omega / (2 ^ (S i))
  else 0.

Definition putnam_2022_a4_solution : R :=
  2 * exp (1 / 2) - 3.

Theorem putnam_2022_a4 :
  forall (A : Type) (P : probability_space A)
         (X : nat -> A -> R)
         (K : A -> set nat) (Svalue : A -> R),
    (forall i : nat, random_variable P (X i)) ->
    (forall i : nat, uniform_on_unit_interval P (X i)) ->
    independent_random_variables P X ->
    stopping_index_set X K ->
    (forall omega : A,
      real_tsum_value
        (fun i : nat => stopped_term X K omega i)
        (Svalue omega)) ->
    lebesgue_integral_value P Svalue putnam_2022_a4_solution.
Admitted.
