(* Statement-only formalization of VERINA corpus artifact verina_basic_65,
   catalog title "SquareRoot": executable computation of the integer square
   root of a natural number by a bounded incrementing loop, together with its
   precondition, square-bound postcondition, and final correctness proposition.
   This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool.

Definition SquareRoot_precond (_N : nat) : Prop :=
  True.

Fixpoint SquareRoot_boundedLoop
    (N bound r : nat) : nat :=
  match bound with
  | O => r
  | S bound' =>
      if Nat.leb ((r + 1) * (r + 1)) N
      then SquareRoot_boundedLoop N bound' (r + 1)
      else r
  end.

Definition SquareRoot
    (N : nat)
    (_h_precond : SquareRoot_precond N) : nat :=
  SquareRoot_boundedLoop N (N + 1) O.

Definition SquareRoot_postcond
    (N result : nat)
    (_h_precond : SquareRoot_precond N) : Prop :=
  (result * result <= N)%nat /\
  (N < (result + 1) * (result + 1))%nat.

Theorem SquareRoot_spec_satisfied
    (N : nat)
    (h_precond : SquareRoot_precond N) :
  SquareRoot_postcond
    N (SquareRoot N h_precond) h_precond.
Admitted.
