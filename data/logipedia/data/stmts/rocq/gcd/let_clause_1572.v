(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.let_clause_1572 (catalog title "gcd.let_clause_1572"): positive n,
  a zero greatest common divisor, and zero equalities for both natural inputs
  imply that the first input is zero. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem let_clause_1572 :
  forall m n : nat,
    0 < n ->
    Nat.gcd m n = 0 ->
    m = 0 ->
    n = 0 ->
    m = 0.
Admitted.
