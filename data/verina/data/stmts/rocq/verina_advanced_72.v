(* Statement-only formalization of VERINA corpus artifact verina_advanced_72,
   catalog title "singleDigitPrimeFactor": executable selection of the
   smallest prime factor among 2, 3, 5, and 7, returning 0 when none applies,
   together with its correctness contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.

Import ListNotations.

Definition singleDigitPrimeFactor_precond (_n : nat) : Prop :=
  True.

Definition singleDigitPrimeFactor
    (n : nat)
    (_h_precond : singleDigitPrimeFactor_precond n) : nat :=
  if Nat.eqb n 0
  then 0
  else if Nat.eqb (Nat.modulo n 2) 0
  then 2
  else if Nat.eqb (Nat.modulo n 3) 0
  then 3
  else if Nat.eqb (Nat.modulo n 5) 0
  then 5
  else if Nat.eqb (Nat.modulo n 7) 0
  then 7
  else 0.

Definition singleDigitPrimeFactor_postcond
    (n result : nat)
    (_h_precond : singleDigitPrimeFactor_precond n) : Prop :=
  In result [0; 2; 3; 5; 7] /\
  (result = 0 ->
    n = 0 \/
    forallb
      (fun factor =>
        negb (Nat.eqb (Nat.modulo n factor) 0))
      [2; 3; 5; 7] = true) /\
  (result <> 0 ->
    n <> 0 /\
    Nat.eqb (Nat.modulo n result) 0 = true /\
    forallb
      (fun x =>
        implb
          (existsb (Nat.eqb x) [2; 3; 5; 7])
          (negb (Nat.eqb (Nat.modulo n x) 0)))
      (seq 0 result) = true).

Theorem singleDigitPrimeFactor_spec_satisfied
    (n : nat)
    (h_precond : singleDigitPrimeFactor_precond n) :
  singleDigitPrimeFactor_postcond
    n
    (singleDigitPrimeFactor n h_precond)
    h_precond.
Admitted.
