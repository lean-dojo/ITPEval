(* Statement-only formalization of VERINA corpus artifact verina_advanced_23,
   catalog title "isPowerOfTwo": an executable fuel-bounded Boolean test for
   whether an integer is a positive power of two, together with its
   correctness contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool ZArith.

Open Scope Z_scope.

Definition isPowerOfTwo_precond (_n : Z) : Prop :=
  True.

Fixpoint isPowerOfTwo_aux
    (m : Z) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      if Z.eqb m 1
      then true
      else
        if Z.eqb (Z.modulo m 2) 0
        then isPowerOfTwo_aux (Z.div m 2) fuel'
        else false
  end.

Definition isPowerOfTwo
    (n : Z)
    (_h_precond : isPowerOfTwo_precond n) : bool :=
  if Z.leb n 0
  then false
  else isPowerOfTwo_aux n (Z.abs_nat n).

Fixpoint isPowerOfTwo_pow
    (base : Z) (exp : nat) : Z :=
  match exp with
  | O => 1
  | S exp' => base * isPowerOfTwo_pow base exp'
  end.

Definition isPowerOfTwo_postcond
    (n : Z)
    (result : bool)
    (_h_precond : isPowerOfTwo_precond n) : Prop :=
  if result
  then
    exists x : nat,
      isPowerOfTwo_pow 2 x = n /\ n > 0
  else
    ~ exists x : nat,
        isPowerOfTwo_pow 2 x = n /\ n > 0.

Theorem isPowerOfTwo_spec_satisfied
    (n : Z)
    (h_precond : isPowerOfTwo_precond n) :
  isPowerOfTwo_postcond
    n (isPowerOfTwo n h_precond) h_precond.
Admitted.
