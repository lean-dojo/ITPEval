(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_lt_plus_r (catalog title "nat.monotonic_lt_plus_r"): adding a
  fixed natural number on the left preserves strict order. This file contains
  no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_monotonic_lt_plus_r :
  forall n x y : nat,
    x < y ->
    Nat.add n x < Nat.add n y.
Admitted.
