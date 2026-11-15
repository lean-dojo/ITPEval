(* Statement-only formalization of PutnamBench corpus artifact putnam_2025_b6
   (putnambench__rocq__putnam_2025_b6): the greatest real exponent admitting
   a positive integer-valued function whose increments dominate an iterated
   value raised to that exponent; this file contains no proof. *)

From Stdlib Require Import Reals Rpower Arith.PeanoNat.

Open Scope R_scope.

Definition putnam_2025_b6_solution : R :=
  1 / 4.

Definition putnam_2025_b6_admissible (r : R) : Prop :=
  exists g : nat -> nat,
    (forall n : nat,
        (0 < n)%nat ->
        (0 < g n)%nat) /\
    forall n : nat,
      (0 < n)%nat ->
      Rpower (INR (g (g n))) r <=
      INR (g ((n + 1)%nat)) - INR (g n).

Definition putnam_2025_b6_is_greatest
    (property : R -> Prop) (greatest : R) : Prop :=
  property greatest /\
  forall candidate : R,
    property candidate ->
    candidate <= greatest.

Theorem putnam_2025_b6 :
  putnam_2025_b6_is_greatest
    putnam_2025_b6_admissible
    putnam_2025_b6_solution.
Admitted.
