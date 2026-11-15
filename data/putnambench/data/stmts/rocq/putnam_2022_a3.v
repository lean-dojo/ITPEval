(* Statement-only formalization of PutnamBench corpus artifact putnam_2022_a3:
   the number of infinite nonzero-residue sequences satisfying a modular
   recurrence is congruent to zero or two modulo five. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat ZArith ZArith.Znumtheory Lists.List.
From Stdlib Require Import Sorting.SetoidList.

Definition putnam_2022_a3_sequence_eq
    (a b : nat -> nat) : Prop :=
  forall n : nat, a n = b n.

Definition putnam_2022_a3_valid_sequence
    (p : nat) (a : nat -> nat) : Prop :=
  forall n : nat,
    (1 <= a n < p)%nat /\
    Nat.modulo (Nat.mul (a n) (a (Nat.add n 2))) p =
      Nat.modulo (Nat.add 1 (a (Nat.add n 1))) p.

Definition putnam_2022_a3_has_cardinality
    (p f : nat) : Prop :=
  exists enumeration : list (nat -> nat),
    NoDupA putnam_2022_a3_sequence_eq enumeration /\
    length enumeration = f /\
    forall a : nat -> nat,
      InA putnam_2022_a3_sequence_eq a enumeration <->
      putnam_2022_a3_valid_sequence p a.

Theorem putnam_2022_a3
    (p f : nat)
    (hp : Znumtheory.prime (Z.of_nat p) /\ (5 < p)%nat)
    (hf : putnam_2022_a3_has_cardinality p f) :
  Nat.modulo f 5%nat = 0%nat \/ Nat.modulo f 5%nat = 2%nat.
Admitted.
