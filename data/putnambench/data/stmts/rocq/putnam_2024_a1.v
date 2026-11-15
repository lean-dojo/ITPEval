(* Statement-only formalization of PutnamBench corpus artifact putnam_2024_a1
   (putnambench__rocq__putnam_2024_a1): the positive natural exponents
   admitting positive natural numbers a, b, and c satisfying
   2*a^n + 3*b^n = 4*c^n are exactly n = 1. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat.

Open Scope nat_scope.

Theorem putnam_2024_a1 :
  forall n : nat,
    (0 < n /\
     exists a b c : nat,
       0 < a /\
       0 < b /\
       0 < c /\
       2 * Nat.pow a n + 3 * Nat.pow b n = 4 * Nat.pow c n) <->
    n = 1.
Admitted.
