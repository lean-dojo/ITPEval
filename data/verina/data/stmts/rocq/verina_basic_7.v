(* Statement-only formalization of VERINA corpus artifact verina_basic_7,
   catalog title "sumOfSquaresOfFirstNOddNumbers": executable accumulation of
   the squares of the first n odd natural numbers, together with its trivial
   precondition, closed-form postcondition, and final correctness proposition.
   This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat.

Definition sumOfSquaresOfFirstNOddNumbers_precond
    (_n : nat) : Prop :=
  True.

Fixpoint sumOfSquaresOfFirstNOddNumbers_loop
    (k sum : nat) : nat :=
  match k with
  | O => sum
  | S k' =>
      sumOfSquaresOfFirstNOddNumbers_loop
        k'
        (sum + (2 * S k' - 1) * (2 * S k' - 1))
  end.

Definition sumOfSquaresOfFirstNOddNumbers
    (n : nat)
    (_h_precond : sumOfSquaresOfFirstNOddNumbers_precond n) : nat :=
  sumOfSquaresOfFirstNOddNumbers_loop n 0.

Definition sumOfSquaresOfFirstNOddNumbers_postcond
    (n result : nat)
    (_h_precond : sumOfSquaresOfFirstNOddNumbers_precond n) : Prop :=
  result - Nat.div (n * (2 * n - 1) * (2 * n + 1)) 3 = 0 /\
  Nat.div (n * (2 * n - 1) * (2 * n + 1)) 3 - result = 0.

Theorem sumOfSquaresOfFirstNOddNumbers_spec_satisfied
    (n : nat)
    (h_precond : sumOfSquaresOfFirstNOddNumbers_precond n) :
  sumOfSquaresOfFirstNOddNumbers_postcond
    n
    (sumOfSquaresOfFirstNOddNumbers n h_precond)
    h_precond.
Admitted.
