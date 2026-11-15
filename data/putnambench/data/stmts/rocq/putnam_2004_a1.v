(* Statement-only formalization of PutnamBench corpus artifact putnam_2004_a1:
   a free-throw success rate crossing 80 percent between two attempt counts
   must equal 80 percent at an intermediate count. This file contains no proof. *)

From Stdlib Require Import Reals Arith.PeanoNat.

Open Scope R_scope.

Fixpoint putnam_2004_a1_successes
    (attempts : nat -> bool) (N : nat) : R :=
  match N with
  | O => 0
  | S n =>
      putnam_2004_a1_successes attempts n +
      if attempts n then 1 else 0
  end.

Definition putnam_2004_a1_solution : Prop := True.

Theorem putnam_2004_a1
    (S : (nat -> bool) -> nat -> R)
    (hS :
      forall (attempts : nat -> bool) (N : nat),
        (1 <= N)%nat ->
        S attempts N =
          putnam_2004_a1_successes attempts N / INR N) :
  (forall (attempts : nat -> bool) (a b : nat),
      (1 <= a)%nat /\
      (a < b)%nat /\
      S attempts a < 4 / 5 /\
      S attempts b > 4 / 5 ->
      exists c : nat,
        (a < c)%nat /\
        (c < b)%nat /\
        S attempts c = 4 / 5) <->
  putnam_2004_a1_solution.
Admitted.
