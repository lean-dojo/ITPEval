(* Statement-only formalization of PutnamBench artifact putnam_1976_b3:
   a lower bound for the intersection probability of a finite sequence of
   events with nonadjacent independence, governed by a positive recurrence.
   This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

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

Definition same_set {A : Type} (E F : set A) : Prop :=
  forall x : A, E x <-> F x.

Definition disjoint {A : Type} (E F : set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition pairwise_disjoint {A : Type} (E : nat -> set A) : Prop :=
  forall m n : nat, m <> n -> disjoint (E m) (E n).

Fixpoint partial_sum (f : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S k => partial_sum f k + f k
  end.

Definition series_sum (f : nat -> R) (s : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (partial_sum f n - s) < epsilon.

Record probability_space (Omega : Type) := {
  ps_measurable : set Omega -> Prop;
  ps_measurable_empty : ps_measurable empty_set;
  ps_measurable_complement :
    forall E : set Omega,
      ps_measurable E ->
      ps_measurable (set_complement E);
  ps_measurable_countable_union :
    forall E : nat -> set Omega,
      (forall n : nat, ps_measurable (E n)) ->
      ps_measurable (countable_union E);
  ps_measure : set Omega -> R;
  ps_measure_extensional :
    forall E F : set Omega,
      same_set E F ->
      ps_measure E = ps_measure F;
  ps_measure_nonnegative :
    forall E : set Omega,
      ps_measurable E ->
      0 <= ps_measure E;
  ps_measure_empty : ps_measure empty_set = 0;
  ps_measure_total : ps_measure full_set = 1;
  ps_measure_countable_additive :
    forall E : nat -> set Omega,
      (forall n : nat, ps_measurable (E n)) ->
      pairwise_disjoint E ->
      series_sum
        (fun n : nat => ps_measure (E n))
        (ps_measure (countable_union E))
}.

Arguments ps_measurable {Omega} _ _.
Arguments ps_measure {Omega} _ _.

Definition independent_events {Omega : Type}
    (P : probability_space Omega) (E F : set Omega) : Prop :=
  ps_measure P (set_intersection E F) =
    ps_measure P E * ps_measure P F.

Definition indices_more_than_one_apart (i j : nat) : Prop :=
  ((i + 1 < j)%nat \/ (j + 1 < i)%nat).

Definition finite_intersection {Omega : Type}
    (events : nat -> set Omega) (n : nat) : set Omega :=
  fun omega =>
    forall i : nat, (i < n)%nat -> events i omega.

Theorem putnam_1976_b3
    (Omega : Type)
    (P : probability_space Omega)
    (n : nat)
    (hn : (1 <= n)%nat)
    (a : R)
    (ha : 0 <= a /\ a < 1 / 4)
    (u : nat -> R)
    (hu01 : u 0%nat = 1 /\ u 1%nat = 1 - a)
    (huk :
      forall k : nat,
        (1 <= k)%nat ->
        u (k + 1)%nat = u k - a * u (k - 1)%nat)
    (hupos : forall k : nat, u k > 0)
    (events : nat -> set Omega)
    (heventsmeas :
      forall i : nat, (i < n)%nat -> ps_measurable P (events i))
    (heventsprob :
      forall i : nat, (i < n)%nat -> ps_measure P (events i) >= 1 - a)
    (heventsindep :
      forall i j : nat,
        (i < n)%nat ->
        (j < n)%nat ->
        indices_more_than_one_apart i j ->
        independent_events P (events i) (events j)) :
  ps_measure P (finite_intersection events n) >= u n.
Admitted.
