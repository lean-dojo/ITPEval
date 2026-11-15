(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.let_clause_1571 (catalog title "gcd.let_clause_1571"): positive n,
  a zero greatest common divisor, and zero equalities for both inputs imply
  that the two natural inputs are equal. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem let_clause_1571 :
  forall m n : nat,
    0 < n ->
    Nat.gcd m n = 0 ->
    m = 0 ->
    n = 0 ->
    m = n.
Admitted.
