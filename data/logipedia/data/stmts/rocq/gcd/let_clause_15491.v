(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.let_clause_15491 (catalog title "gcd.let_clause_15491"): if a natural
  number n is zero, every natural x is unchanged by truncated subtraction of
  n, uniformly for an arbitrary natural parameter m. This file contains no
  proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem let_clause_15491 :
  forall m : nat,
    forall n : nat,
      O = n ->
      forall x1106 : nat,
        x1106 = x1106 - n.
Admitted.
