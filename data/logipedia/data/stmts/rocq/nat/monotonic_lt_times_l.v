(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_lt_times_l (catalog title "nat.monotonic_lt_times_l"):
  multiplication on the right by a positive natural number is strictly
  monotone. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_monotonic_lt_times_l :
  forall c : nat,
    Nat.lt 0 c ->
    forall x y : nat,
      Nat.lt x y ->
      Nat.lt (Nat.mul x c) (Nat.mul y c).
Admitted.
