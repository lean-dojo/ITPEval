(*
  Statement-only formalization of "Buffon Needle Problem" from Hundred
  Theorems artifact 099. It states the crossing probabilities for a needle
  whose distance to the nearest ruled line and angle are independent uniform
  real random variables, in both the short- and long-needle cases. This file
  contains no proof.
*)

From Stdlib Require Import Reals.

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
  | O => u O
  | S k => partial_sum u k + u (S k)
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
        (fun n => ps_measure (E n))
        (ps_measure (countable_union E))
}.

Definition measurable_real_function {A : Type}
    (measurable : set A -> Prop) (f : A -> R) : Prop :=
  forall B : set R,
    borel_set B ->
    measurable (preimage f B).

Definition random_variable {A : Type}
    (P : probability_space A) (X : A -> R) : Prop :=
  measurable_real_function (ps_measurable P) X.

Definition uniform_on_interval {A : Type}
    (P : probability_space A) (X : A -> R) (a b : R) : Prop :=
  random_variable P X /\
  a < b /\
  forall t : R,
    (t < a -> ps_measure P (fun w => X w <= t) = 0) /\
    (b <= t -> ps_measure P (fun w => X w <= t) = 1) /\
    (a <= t < b ->
      ps_measure P (fun w => X w <= t) = (t - a) / (b - a)).

Definition independent_real_random_variables {A : Type}
    (P : probability_space A) (X Y : A -> R) : Prop :=
  random_variable P X /\
  random_variable P Y /\
  forall B C : set R,
    borel_set B ->
    borel_set C ->
    ps_measure P
      (set_intersection (preimage X B) (preimage Y C)) =
    ps_measure P (preimage X B) * ps_measure P (preimage Y C).

Definition needle_crosses {A : Type}
    (X Theta : A -> R) (length : R) : set A :=
  fun w => X w <= (length / 2) * sin (Theta w).

Theorem buffon_needle_problem :
  forall (A : Type) (P : probability_space A)
         (X Theta : A -> R) (length spacing : R),
    0 < length ->
    0 < spacing ->
    uniform_on_interval P X 0 (spacing / 2) ->
    uniform_on_interval P Theta 0 PI ->
    independent_real_random_variables P X Theta ->
    (length <= spacing ->
      ps_measure P (needle_crosses X Theta length) =
      (2 * length) / (PI * spacing)) /\
    (spacing <= length ->
      ps_measure P (needle_crosses X Theta length) =
      (2 / (PI * spacing)) *
        (length - sqrt (length ^ 2 - spacing ^ 2) +
         spacing * acos (spacing / length))).
Admitted.
