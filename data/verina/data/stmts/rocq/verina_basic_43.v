(* Statement-only formalization of VERINA corpus artifact verina_basic_43,
   catalog title "sumOfFourthPowerOfOddNumbers": an executable recursive sum
   of the fourth powers of the first n odd natural numbers, together with its
   trivial precondition, closed-form postcondition, and final correctness
   proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat.

Definition sumOfFourthPowerOfOddNumbers_precond (_n : nat) : Prop :=
  True.

Fixpoint sumOfFourthPowerOfOddNumbers
    (n : nat)
    (_h_precond : sumOfFourthPowerOfOddNumbers_precond n) : nat :=
  match n with
  | O => O
  | S k =>
      let prev :=
        sumOfFourthPowerOfOddNumbers k _h_precond in
      let nextOdd := 2 * k + 1 in
      prev + Nat.pow nextOdd 4
  end.

Definition sumOfFourthPowerOfOddNumbers_postcond
    (n result : nat)
    (_h_precond : sumOfFourthPowerOfOddNumbers_precond n) : Prop :=
  15 * result =
    (n * (2 * n + 1)) *
      Nat.sub
        (Nat.sub
          (7 + 24 * Nat.pow n 3)
          (12 * Nat.pow n 2))
        (14 * n).

Theorem sumOfFourthPowerOfOddNumbers_spec_satisfied
    (n : nat)
    (h_precond : sumOfFourthPowerOfOddNumbers_precond n) :
  sumOfFourthPowerOfOddNumbers_postcond
    n
    (sumOfFourthPowerOfOddNumbers n h_precond)
    h_precond.
Admitted.
