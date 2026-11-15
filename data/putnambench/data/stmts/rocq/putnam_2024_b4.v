(* Statement-only formalization of PutnamBench corpus artifact putnam_2024_b4
   (putnambench__rocq__putnam_2024_b4): the normalized expected position of
   the independent uniform integer-driven walk converges to
   (1 - exp(-2))/2. This file contains no proof. *)

From Stdlib Require Import Reals ZArith Arith.PeanoNat.

Set Implicit Arguments.
Open Scope R_scope.

Definition putnam_2024_b4_event (A : Type) := A -> Prop.

Definition putnam_2024_b4_empty_event {A : Type} :
    putnam_2024_b4_event A :=
  fun _ => False.

Definition putnam_2024_b4_full_event {A : Type} :
    putnam_2024_b4_event A :=
  fun _ => True.

Definition putnam_2024_b4_event_complement {A : Type}
    (E : putnam_2024_b4_event A) : putnam_2024_b4_event A :=
  fun x => ~ E x.

Definition putnam_2024_b4_event_intersection {A : Type}
    (E F : putnam_2024_b4_event A) : putnam_2024_b4_event A :=
  fun x => E x /\ F x.

Definition putnam_2024_b4_countable_union {A : Type}
    (E : nat -> putnam_2024_b4_event A) : putnam_2024_b4_event A :=
  fun x => exists n : nat, E n x.

Definition putnam_2024_b4_same_event {A : Type}
    (E F : putnam_2024_b4_event A) : Prop :=
  forall x : A, E x <-> F x.

Definition putnam_2024_b4_disjoint_events {A : Type}
    (E F : putnam_2024_b4_event A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition putnam_2024_b4_pairwise_disjoint {A : Type}
    (E : nat -> putnam_2024_b4_event A) : Prop :=
  forall i j : nat,
    i <> j ->
    putnam_2024_b4_disjoint_events (E i) (E j).

Fixpoint putnam_2024_b4_finite_sum
    (count : nat) (u : nat -> R) : R :=
  match count with
  | O => 0
  | S k => putnam_2024_b4_finite_sum k u + u k
  end.

Definition putnam_2024_b4_sequence_converges
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists cutoff : nat,
      forall n : nat,
        (cutoff <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Definition putnam_2024_b4_series_sum
    (u : nat -> R) (sum : R) : Prop :=
  putnam_2024_b4_sequence_converges
    (fun count => putnam_2024_b4_finite_sum count u)
    sum.

Record putnam_2024_b4_probability_space (A : Type) := {
  putnam_2024_b4_measurable :
    putnam_2024_b4_event A -> Prop;
  putnam_2024_b4_measurable_extensional :
    forall E F : putnam_2024_b4_event A,
      putnam_2024_b4_same_event E F ->
      putnam_2024_b4_measurable E ->
      putnam_2024_b4_measurable F;
  putnam_2024_b4_measurable_empty :
    putnam_2024_b4_measurable putnam_2024_b4_empty_event;
  putnam_2024_b4_measurable_complement :
    forall E : putnam_2024_b4_event A,
      putnam_2024_b4_measurable E ->
      putnam_2024_b4_measurable
        (putnam_2024_b4_event_complement E);
  putnam_2024_b4_measurable_countable_union :
    forall E : nat -> putnam_2024_b4_event A,
      (forall n : nat, putnam_2024_b4_measurable (E n)) ->
      putnam_2024_b4_measurable
        (putnam_2024_b4_countable_union E);
  putnam_2024_b4_measure :
    putnam_2024_b4_event A -> R;
  putnam_2024_b4_measure_extensional :
    forall E F : putnam_2024_b4_event A,
      putnam_2024_b4_same_event E F ->
      putnam_2024_b4_measure E = putnam_2024_b4_measure F;
  putnam_2024_b4_measure_nonnegative :
    forall E : putnam_2024_b4_event A,
      putnam_2024_b4_measurable E ->
      0 <= putnam_2024_b4_measure E;
  putnam_2024_b4_measure_empty :
    putnam_2024_b4_measure putnam_2024_b4_empty_event = 0;
  putnam_2024_b4_measure_total :
    putnam_2024_b4_measure putnam_2024_b4_full_event = 1;
  putnam_2024_b4_measure_countable_additive :
    forall E : nat -> putnam_2024_b4_event A,
      (forall n : nat, putnam_2024_b4_measurable (E n)) ->
      putnam_2024_b4_pairwise_disjoint E ->
      putnam_2024_b4_series_sum
        (fun n => putnam_2024_b4_measure (E n))
        (putnam_2024_b4_measure
          (putnam_2024_b4_countable_union E))
}.

Definition putnam_2024_b4_preimage
    {A : Type} (X : A -> Z) (values : Z -> Prop) :
    putnam_2024_b4_event A :=
  fun omega => values (X omega).

Definition putnam_2024_b4_value_event
    {A : Type} (X : A -> Z) (value : Z) :
    putnam_2024_b4_event A :=
  fun omega => X omega = value.

Definition putnam_2024_b4_integer_random_variable
    {A : Type} (P : putnam_2024_b4_probability_space A)
    (X : A -> Z) : Prop :=
  forall values : Z -> Prop,
    putnam_2024_b4_measurable P
      (putnam_2024_b4_preimage X values).

Definition putnam_2024_b4_integer_interval_contains
    (n : nat) (value : Z) : Prop :=
  (1 <= value <= Z.of_nat n)%Z.

Definition putnam_2024_b4_uniform_atom_mass
    (n : nat) (value : Z) : R :=
  if Z_le_dec 1 value then
    if Z_le_dec value (Z.of_nat n) then / INR n else 0
  else 0.

Definition putnam_2024_b4_uniform_integer_choice
    {A : Type} (P : putnam_2024_b4_probability_space A)
    (n : nat) (X : A -> Z) : Prop :=
  putnam_2024_b4_integer_random_variable P X /\
  putnam_2024_b4_measure P
    (fun omega =>
      putnam_2024_b4_integer_interval_contains n (X omega)) = 1 /\
  forall value : Z,
    putnam_2024_b4_measure P
      (putnam_2024_b4_value_event X value) =
    putnam_2024_b4_uniform_atom_mass n value.

Definition putnam_2024_b4_distinct_index_pairs
    (rows steps : nat -> nat) (count : nat) : Prop :=
  forall i j : nat,
    (i < count)%nat ->
    (j < count)%nat ->
    rows i = rows j ->
    steps i = steps j ->
    i = j.

Fixpoint putnam_2024_b4_finite_preimage_intersection
    {A : Type}
    (X : nat -> nat -> A -> Z)
    (rows steps : nat -> nat)
    (values : nat -> Z -> Prop)
    (count : nat) : putnam_2024_b4_event A :=
  match count with
  | O => putnam_2024_b4_full_event
  | S k =>
      putnam_2024_b4_event_intersection
        (putnam_2024_b4_finite_preimage_intersection
          X rows steps values k)
        (putnam_2024_b4_preimage
          (X (rows k) (steps k)) (values k))
  end.

Fixpoint putnam_2024_b4_finite_probability_product
    {A : Type}
    (P : putnam_2024_b4_probability_space A)
    (X : nat -> nat -> A -> Z)
    (rows steps : nat -> nat)
    (values : nat -> Z -> Prop)
    (count : nat) : R :=
  match count with
  | O => 1
  | S k =>
      putnam_2024_b4_finite_probability_product
        P X rows steps values k *
      putnam_2024_b4_measure P
        (putnam_2024_b4_preimage
          (X (rows k) (steps k)) (values k))
  end.

Definition putnam_2024_b4_mutually_independent
    {A : Type} (P : putnam_2024_b4_probability_space A)
    (X : nat -> nat -> A -> Z) : Prop :=
  (forall row step : nat,
      putnam_2024_b4_integer_random_variable P (X row step)) /\
  forall (rows steps : nat -> nat)
         (values : nat -> Z -> Prop)
         (count : nat),
    putnam_2024_b4_distinct_index_pairs rows steps count ->
    putnam_2024_b4_measure P
      (putnam_2024_b4_finite_preimage_intersection
        X rows steps values count) =
    putnam_2024_b4_finite_probability_product
      P X rows steps values count.

Fixpoint putnam_2024_b4_integer_expectation_sum
    {A : Type}
    (P : putnam_2024_b4_probability_space A)
    (X : A -> Z) (bound count : nat) : R :=
  match count with
  | O => 0
  | S k =>
      let value := (Z.of_nat k - Z.of_nat bound)%Z in
      putnam_2024_b4_integer_expectation_sum P X bound k +
      IZR value *
        putnam_2024_b4_measure P
          (putnam_2024_b4_value_event X value)
  end.

Definition putnam_2024_b4_bounded_integer_expectation
    {A : Type}
    (P : putnam_2024_b4_probability_space A)
    (X : A -> Z) (bound : nat) : R :=
  putnam_2024_b4_integer_expectation_sum
    P X bound ((2 * bound + 1)%nat).

Definition putnam_2024_b4_solution : R :=
  (1 - exp (-2)) / 2.

Definition putnam_2024_b4_normalized_expected_position
    {A : Type}
    (P : putnam_2024_b4_probability_space A)
    (a : nat -> nat -> A -> Z) (n : nat) : R :=
  putnam_2024_b4_bounded_integer_expectation
    P (a n n) (S n) / INR n.

Theorem putnam_2024_b4 :
  forall
    (A : Type)
    (P : putnam_2024_b4_probability_space A)
    (m a : nat -> nat -> A -> Z),
    (forall n : nat,
      (0 < n)%nat ->
      forall omega : A, a n O omega = 1%Z) ->
    (forall n k : nat,
      (0 < n)%nat ->
      putnam_2024_b4_uniform_integer_choice P n (m n k)) ->
    (forall (n k : nat) (omega : A),
      (0 < n)%nat ->
      a n (S k) omega =
        if Z_lt_dec (a n k omega) (m n k omega) then
          (a n k omega + 1)%Z
        else if Z.eq_dec (m n k omega) (a n k omega) then
          a n k omega
        else
          (a n k omega - 1)%Z) ->
    putnam_2024_b4_mutually_independent P m ->
    putnam_2024_b4_sequence_converges
      (putnam_2024_b4_normalized_expected_position P a)
      putnam_2024_b4_solution.
Admitted.
