(* Statement-only formalization of PutnamBench artifact putnam_1965_b1:
   the limit of the repeated unit-cube integrals of the squared cosine of
   the normalized coordinate sum. This file contains no proof. *)

From Stdlib Require Import Reals List.

Import ListNotations.
Open Scope R_scope.

Definition putnam_1965_b1_solution : R := 1 / 2.

Fixpoint putnam_1965_b1_coordinate_sum (coordinates : list R) : R :=
  match coordinates with
  | nil => 0
  | x :: rest => x + putnam_1965_b1_coordinate_sum rest
  end.

Fixpoint putnam_1965_b1_iterated_unit_integral
    (dimension : nat) (f : list R -> R) (value : R) : Prop :=
  match dimension with
  | O => value = f nil
  | S lower_dimension =>
      exists slice_integral : R -> R,
        (forall x : R,
          putnam_1965_b1_iterated_unit_integral
            lower_dimension
            (fun remaining_coordinates : list R =>
              f (x :: remaining_coordinates))
            (slice_integral x)) /\
        exists integrable : Riemann_integrable slice_integral 0 1,
          value = RiemannInt integrable
  end.

Definition putnam_1965_b1_term (n : nat) (value : R) : Prop :=
  putnam_1965_b1_iterated_unit_integral
    (S n)
    (fun coordinates : list R =>
      cos
        (PI / (2 * INR (S n)) *
          putnam_1965_b1_coordinate_sum coordinates) ^ 2)
    value.

Definition putnam_1965_b1_relational_sequence_converges
    (term : nat -> R -> Prop) (limit : R) : Prop :=
  (forall n : nat, exists value : R, term n value) /\
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall (n : nat) (value : R),
        (N <= n)%nat ->
        term n value ->
        Rabs (value - limit) < epsilon.

Theorem putnam_1965_b1 :
  putnam_1965_b1_relational_sequence_converges
    putnam_1965_b1_term
    putnam_1965_b1_solution.
Admitted.
