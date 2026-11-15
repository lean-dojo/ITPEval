(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.let_clause_1551 (catalog title "gcd.let_clause_1551"): if a natural
  number n is zero, multiplying n by any natural number leaves n unchanged;
  the source also quantifies an arbitrary natural m. This file contains no
  proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem let_clause_1551 :
  forall m n : nat,
    O = n ->
    forall x347 : nat,
      n = x347 * n.
Admitted.
