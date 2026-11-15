(* Statement-only formalization of VERINA corpus artifact verina_advanced_9,
   catalog title "countSumDivisibleBy": an executable count of natural numbers
   below n whose decimal digit sum is divisible by a positive divisor d,
   together with its exact filtered-list correctness contract. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.

Import ListNotations.

Fixpoint sumOfDigits_go
    (fuel n acc : nat) : nat :=
  match fuel with
  | O => acc
  | S fuel' =>
      if Nat.eqb n 0
      then acc
      else
        sumOfDigits_go
          fuel' (Nat.div n 10) (acc + Nat.modulo n 10)
  end.

Definition sumOfDigits (x : nat) : nat :=
  sumOfDigits_go x x 0%nat.

Definition countSumDivisibleBy_precond
    (_n d : nat) : Prop :=
  (0 < d)%nat.

Definition isSumDivisibleBy
    (x d : nat) : bool :=
  Nat.eqb (Nat.modulo (sumOfDigits x) d) 0%nat.

Fixpoint countSumDivisibleBy_go
    (i acc d : nat) : nat :=
  match i with
  | O => acc
  | S i' =>
      let acc' :=
        if isSumDivisibleBy i' d then S acc else acc in
      countSumDivisibleBy_go i' acc' d
  end.

Definition countSumDivisibleBy
    (n d : nat)
    (_h_precond : countSumDivisibleBy_precond n d) : nat :=
  countSumDivisibleBy_go n 0%nat d.

Definition countSumDivisibleBy_expected
    (n d : nat) : nat :=
  length
    (filter
      (fun x =>
        andb
          (Nat.ltb x n)
          (Nat.eqb
            (Nat.modulo (sumOfDigits x) d)
            0%nat))
      (seq 0%nat n)).

Definition countSumDivisibleBy_postcond
    (n d result : nat)
    (_h_precond : countSumDivisibleBy_precond n d) : Prop :=
  Nat.sub (countSumDivisibleBy_expected n d) result = 0%nat /\
  (result <= countSumDivisibleBy_expected n d)%nat.

Theorem countSumDivisibleBy_spec_satisfied
    (n d : nat)
    (h_precond : countSumDivisibleBy_precond n d) :
  countSumDivisibleBy_postcond
    n d (countSumDivisibleBy n d h_precond) h_precond.
Admitted.
