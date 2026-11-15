(* Statement-only formalization of VERINA corpus artifact verina_basic_28,
   catalog title "isPrime": an executable fuel-bounded divisibility test for
   natural numbers at least 2, together with its all-divisors/exists-divisor
   postcondition and final correctness proposition. This file contains no
   proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.

Definition isPrime_precond (n : nat) : Prop :=
  (2 <= n)%nat.

Fixpoint isPrime_check
    (n i fuel : nat) : bool :=
  match fuel with
  | 0%nat => true
  | S fuel' =>
      if Nat.ltb n (Nat.mul i i) then
        true
      else if Nat.eqb (Nat.modulo n i) 0%nat then
        false
      else
        isPrime_check n (S i) fuel'
  end.

Definition isPrime
    (n : nat)
    (_h_precond : isPrime_precond n) : bool :=
  isPrime_check n 2%nat n.

Definition isPrime_postcond
    (n : nat)
    (result : bool)
    (_h_precond : isPrime_precond n) : Prop :=
  (Is_true result ->
    forallb
      (fun k => negb (Nat.eqb (Nat.modulo n k) 0%nat))
      (seq 2%nat (Nat.sub n 2%nat)) = true) /\
  (~ Is_true result ->
    existsb
      (fun k => Nat.eqb (Nat.modulo n k) 0%nat)
      (seq 2%nat (Nat.sub n 2%nat)) = true).

Theorem isPrime_spec_satisfied
    (n : nat)
    (h_precond : isPrime_precond n) :
  isPrime_postcond n (isPrime n h_precond) h_precond.
Admitted.
