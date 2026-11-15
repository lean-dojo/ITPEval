(* Statement-only formalization of VERINA corpus artifact verina_basic_11,
   catalog title "lastDigit": the executable remainder computation giving
   the last decimal digit of a natural number, together with its correctness
   contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat.

Definition lastDigit_precond (_n : nat) : Prop :=
  True.

Definition lastDigit
    (n : nat)
    (_h_precond : lastDigit_precond n) : nat :=
  Nat.modulo n 10.

Definition lastDigit_postcond
    (n result : nat)
    (_h_precond : lastDigit_precond n) : Prop :=
  (Nat.le 0 result /\ Nat.lt result 10) /\
  (Nat.sub (Nat.modulo n 10) result = 0 /\
   Nat.sub result (Nat.modulo n 10) = 0).

Theorem lastDigit_spec_satisfied
    (n : nat)
    (h_precond : lastDigit_precond n) :
  lastDigit_postcond n (lastDigit n h_precond) h_precond.
Admitted.
