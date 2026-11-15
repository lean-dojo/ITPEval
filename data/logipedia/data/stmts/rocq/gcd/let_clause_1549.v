(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.let_clause_1549 (catalog title "gcd.let_clause_1549"): if a natural
  number n is positive and m is zero, every natural x is unchanged by
  truncated subtraction of m. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem let_clause_1549 :
  forall m n : nat,
    O < n ->
    O = m ->
    forall x1106 : nat,
      x1106 = x1106 - m.
Admitted.
