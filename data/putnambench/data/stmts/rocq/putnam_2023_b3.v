(* Statement-only formalization of PutnamBench corpus artifact putnam_2023_b3:
   the expected length of the longest zigzag subsequence of independent
   uniform unit-interval real variables is (2n + 2)/3. This file contains no
   proof. *)

From Stdlib Require Import Reals Lists.List Arith.PeanoNat RiemannInt.

Import ListNotations.
Open Scope R_scope.

Definition putnam_2023_b3_in_unit_cube (coordinates : list R) : Prop :=
  Forall (fun x : R => 0 <= x <= 1) coordinates.

Definition putnam_2023_b3_is_zigzag
    (k : nat) (y : nat -> R) : Prop :=
  (k = 1)%nat \/
  ((forall i : nat,
      (S i < k)%nat ->
      y (S i) <> y i) /\
   (forall i : nat,
      (S (S i) < k)%nat ->
      (y (S (S i)) < y (S i) <-> y i < y (S i)))).

Definition putnam_2023_b3_increasing_indices
    (n k : nat) (indices : nat -> nat) : Prop :=
  (forall j : nat,
      (j < k)%nat ->
      (indices j < n)%nat) /\
  (forall i j : nat,
      (i < j)%nat ->
      (j < k)%nat ->
      (indices i < indices j)%nat).

Definition putnam_2023_b3_admissible_length
    (n : nat) (coordinates : list R) (k : nat) : Prop :=
  (0 < k)%nat /\
  exists indices : nat -> nat,
    putnam_2023_b3_increasing_indices n k indices /\
    putnam_2023_b3_is_zigzag
      k
      (fun j : nat => nth (indices j) coordinates 0).

Definition putnam_2023_b3_is_greatest
    (property : nat -> Prop) (greatest : nat) : Prop :=
  property greatest /\
  forall k : nat, property k -> (k <= greatest)%nat.

Fixpoint putnam_2023_b3_iterated_unit_integral
    (dimension : nat) (f : list R -> R) (value : R) : Prop :=
  match dimension with
  | O => value = f []
  | S lower_dimension =>
      exists slice_integral : R -> R,
        (forall x : R,
          0 <= x <= 1 ->
          putnam_2023_b3_iterated_unit_integral
            lower_dimension
            (fun remaining_coordinates : list R =>
              f (x :: remaining_coordinates))
            (slice_integral x)) /\
        exists integrable : Riemann_integrable slice_integral 0 1,
          value = RiemannInt integrable
  end.

Definition putnam_2023_b3_solution (n : nat) : R :=
  (2 * INR n + 2) / 3.

Theorem putnam_2023_b3 :
  forall (n : nat) (a : list R -> nat),
    (2 <= n)%nat ->
    (forall coordinates : list R,
      length coordinates = n ->
      putnam_2023_b3_in_unit_cube coordinates ->
      putnam_2023_b3_is_greatest
        (putnam_2023_b3_admissible_length n coordinates)
        (a coordinates)) ->
    putnam_2023_b3_iterated_unit_integral
      n
      (fun coordinates : list R => INR (a coordinates))
      (putnam_2023_b3_solution n).
Admitted.
