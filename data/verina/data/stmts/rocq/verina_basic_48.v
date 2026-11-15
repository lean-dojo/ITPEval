(* Statement-only formalization of VERINA corpus artifact verina_basic_48,
   catalog title "isPerfectSquare": an executable fuel-bounded search deciding
   whether a natural number is a perfect square, together with its trivial
   precondition, exact square-existence postcondition, and final correctness
   proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool.

Definition isPerfectSquare_precond (_n : nat) : Prop :=
  True.

Fixpoint isPerfectSquare_check
    (n x fuel : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      if Nat.ltb n (x * x)
      then false
      else
        if Nat.eqb (x * x) n
        then true
        else isPerfectSquare_check n (x + 1) fuel'
  end.

Definition isPerfectSquare
    (n : nat)
    (_h_precond : isPerfectSquare_precond n) : bool :=
  if Nat.eqb n 0
  then true
  else isPerfectSquare_check n 1 n.

Definition isPerfectSquare_postcond
    (n : nat)
    (result : bool)
    (_h_precond : isPerfectSquare_precond n) : Prop :=
  result = true <->
  exists i : nat, i * i = n.

Theorem isPerfectSquare_spec_satisfied
    (n : nat)
    (h_precond : isPerfectSquare_precond n) :
  isPerfectSquare_postcond
    n (isPerfectSquare n h_precond) h_precond.
Admitted.
