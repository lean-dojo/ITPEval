(* Statement-only formalization of VERINA corpus artifact verina_basic_81,
   catalog title "DivisionFunction": executable natural-number division
   returning an integer remainder-quotient pair, with a safe zero-divisor
   branch, its unconditional precondition, postcondition, and final
   correctness proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool ZArith.

Definition DivisionFunction_precond
    (_x _y : nat) : Prop :=
  True.

Definition divMod (x y : nat) : Z * Z :=
  let q := Z.of_nat (Nat.div x y) in
  let r := Z.of_nat (Nat.modulo x y) in
  (r, q).

Definition DivisionFunction
    (x y : nat)
    (_h_precond : DivisionFunction_precond x y) : Z * Z :=
  if Nat.eqb y 0%nat
  then (Z.of_nat x, 0%Z)
  else divMod x y.

Definition DivisionFunction_postcond
    (x y : nat)
    (result : Z * Z)
    (_h_precond : DivisionFunction_precond x y) : Prop :=
  let r := fst result in
  let q := snd result in
  (y = 0%nat -> r = Z.of_nat x /\ q = 0%Z) /\
  (y <> 0%nat ->
    (q * Z.of_nat y + r = Z.of_nat x)%Z /\
    ((0 <= r)%Z /\ (r < Z.of_nat y)%Z) /\
    (0 <= q)%Z).

Theorem DivisionFunction_spec_satisfied
    (x y : nat)
    (h_precond : DivisionFunction_precond x y) :
  DivisionFunction_postcond
    x y (DivisionFunction x y h_precond) h_precond.
Admitted.
