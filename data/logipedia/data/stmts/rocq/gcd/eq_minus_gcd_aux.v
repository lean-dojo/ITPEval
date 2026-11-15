(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.eq_minus_gcd_aux (catalog title "gcd.eq_minus_gcd_aux"): for positive
  natural n bounded by m and the recursion fuel p, natural coefficients
  witness that one of two truncated differences of multiples equals the
  fuel-recursive auxiliary gcd value. This file contains no proof.
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

Theorem eq_minus_gcd_aux :
  forall p m n : nat,
    O < n ->
    n <= m ->
    n <= p ->
    exists a b : nat,
      a * n - b * m = gcd_aux p m n \/
      b * m - a * n = gcd_aux p m n.
Admitted.
