(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.let_clause_1544 (catalog title "gcd.let_clause_1544"): a nested
  natural-number statement about fuel-recursive gcd values and Bezout-style
  truncated differences, concluding that exchanging the order of the factors
  in one product preserves the stated equality. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Fixpoint gcd_aux (p m n : nat) : nat :=
  match p with
  | O => m
  | S q =>
      if Nat.eqb (Nat.modulo m n) O
      then n
      else gcd_aux q n (Nat.modulo m n)
  end.

Definition gcd_divides (divisor value : nat) : Prop :=
  exists quotient : nat, value = divisor * quotient.

Theorem let_clause_1544 :
  forall p q : nat,
    (forall m n : nat,
      O < n ->
      n <= m ->
      n <= q ->
      exists a b : nat,
        a * n - b * m = gcd_aux q m n \/
        b * m - a * n = gcd_aux q m n) ->
    forall m n : nat,
      O < n ->
      n <= m ->
      n <= S q ->
      ~ gcd_divides n m ->
      forall a : nat,
        (exists b : nat,
          a * (Nat.modulo m n) - b * n =
            gcd_aux q n (Nat.modulo m n) \/
          b * n - a * (Nat.modulo m n) =
            gcd_aux q n (Nat.modulo m n)) ->
        forall b : nat,
          (a * (Nat.modulo m n) - b * n =
             gcd_aux q n (Nat.modulo m n) \/
           b * n - a * (Nat.modulo m n) =
             gcd_aux q n (Nat.modulo m n)) ->
          a * (Nat.modulo m n) - b * n =
            gcd_aux q n (Nat.modulo m n) ->
          a * (Nat.modulo m n) - n * b =
            gcd_aux q n (Nat.modulo m n).
Admitted.
