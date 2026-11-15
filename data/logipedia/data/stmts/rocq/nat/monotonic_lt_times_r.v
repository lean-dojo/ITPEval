(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_lt_times_r (catalog title "nat.monotonic_lt_times_r"):
  multiplication on the left by a positive natural number is strictly
  monotone. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_monotonic_lt_times_r :
  forall c : nat,
    Nat.lt 0 c ->
    forall x y : nat,
      Nat.lt x y ->
      Nat.lt (Nat.mul c x) (Nat.mul c y).
Admitted.
