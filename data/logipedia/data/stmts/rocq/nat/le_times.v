(*
  Statement-only formalization of Logipedia corpus artifact nat.le_times
  (catalog title "nat.le_times"): multiplication on natural numbers is
  monotone in both arguments. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_times :
  forall n1 n2 m1 m2 : nat,
    n1 <= n2 ->
    m1 <= m2 ->
    Nat.mul n1 m1 <= Nat.mul n2 m2.
Admitted.
