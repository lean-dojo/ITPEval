(* Statement-only formalization of PutnamBench artifact putnam_1968_b1:
   the probability that the minimum of two finite-range integer-valued random
   variables equals k, expressed using their point probabilities and the
   corresponding maximum event. This file contains no proof. *)

From Stdlib Require Import Reals ZArith List.

Open Scope R_scope.

Definition set (A : Type) := A -> Prop.

Definition empty_set {A : Type} : set A :=
  fun _ => False.

Definition full_set {A : Type} : set A :=
  fun _ => True.

Definition set_complement {A : Type} (E : set A) : set A :=
  fun x => ~ E x.

Definition countable_union {A : Type} (E : nat -> set A) : set A :=
  fun x => exists n : nat, E n x.

Definition preimage {A B : Type} (f : A -> B) (E : set B) : set A :=
  fun x => E (f x).

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

Definition measurable_integer_function {Omega : Type}
    (P : probability_space Omega) (X : Omega -> Z) : Prop :=
  forall E : set Z,
    ps_measurable P (preimage X E).

Definition finite_range {A B : Type} (f : A -> B) : Prop :=
  exists values : list B,
    forall x : A, In (f x) values.

Definition putnam_1968_b1_solution
    (p1 p2 p3 : R) : R :=
  p1 + p2 - p3.

Theorem putnam_1968_b1
    (Omega : Type)
    (P : probability_space Omega)
    (X Y : Omega -> Z)
    (hX : measurable_integer_function P X)
    (hY : measurable_integer_function P Y)
    (hXfinite : finite_range X)
    (hYfinite : finite_range Y)
    (k : Z) :
  ps_measure P
      (fun omega : Omega => Z.min (X omega) (Y omega) = k) =
    putnam_1968_b1_solution
      (ps_measure P (fun omega : Omega => X omega = k))
      (ps_measure P (fun omega : Omega => Y omega = k))
      (ps_measure P
        (fun omega : Omega => Z.max (X omega) (Y omega) = k)).
Admitted.
