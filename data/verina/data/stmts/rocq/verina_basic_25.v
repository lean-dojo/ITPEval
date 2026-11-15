(* Statement-only formalization of VERINA corpus artifact verina_basic_25,
   catalog title "sumAndAverage": the executable sum of the naturals from
   zero through a positive bounded input and its IEEE binary64 average,
   together with the precondition, postcondition, and final correctness
   proposition. This file contains no proof. *)

From Stdlib Require Import
  Arith.PeanoNat Bool.Bool Floats.FloatOps Floats.PrimFloat
  Floats.SpecFloat Lists.List ZArith.

Import ListNotations.

Definition sumAndAverage_nat_to_float (n : nat) : float :=
  SF2Prim
    (binary_normalize prec emax (Z.of_nat n) Z0 false).

Definition sumAndAverage_precond (n : nat) : Prop :=
  (0 < n)%nat /\ (n < 9007199254740992)%nat.

Definition sumAndAverage_sum (n : nat) : nat :=
  fold_right Nat.add 0%nat (seq 0%nat (S n)).

Definition sumAndAverage
    (n : nat)
    (_h_precond : sumAndAverage_precond n)
    : (Z * float)%type :=
  if Nat.leb n 0%nat then
    (0%Z, PrimFloat.zero)
  else
    let sum := sumAndAverage_sum n in
    let average :=
      PrimFloat.div
        (sumAndAverage_nat_to_float sum)
        (sumAndAverage_nat_to_float n) in
    (Z.of_nat sum, average).

Definition sumAndAverage_pair_eqb
    (x y : (Z * float)%type) : bool :=
  andb
    (Z.eqb (fst x) (fst y))
    (PrimFloat.eqb (snd x) (snd y)).

Definition sumAndAverage_postcond
    (n : nat)
    (result : (Z * float)%type)
    (_h_precond : sumAndAverage_precond n) : Prop :=
  (n = 0%nat ->
    sumAndAverage_pair_eqb
      result (0%Z, PrimFloat.zero) = true) /\
  ((0 < n)%nat ->
    let expected_sum :=
      Nat.div (Nat.mul n (Nat.add n 1%nat)) 2%nat in
    Z.eqb (fst result) (Z.of_nat expected_sum) = true /\
    PrimFloat.eqb
      (snd result)
      (PrimFloat.div
        (sumAndAverage_nat_to_float expected_sum)
        (sumAndAverage_nat_to_float n)) = true).

Theorem sumAndAverage_spec_satisfied
    (n : nat)
    (h_precond : sumAndAverage_precond n) :
  sumAndAverage_postcond
    n (sumAndAverage n h_precond) h_precond.
Admitted.
