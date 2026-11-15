(*
  Statement-only formalization of Thousand Theorems corpus artifact Q756946
  (thousand-theorems__rocq__Q756946), "Lagrange's four-square theorem":
  every natural number is a sum of four squares of natural numbers. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem lagrange_four_square_theorem :
  forall n : nat,
    exists a b c d : nat,
      Nat.add
        (Nat.add
          (Nat.add (Nat.pow a 2) (Nat.pow b 2))
          (Nat.pow c 2))
        (Nat.pow d 2) = n.
Admitted.
