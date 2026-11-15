(*
  Statement-only formalization of Logipedia corpus artifact
  nat.injective_plus_r (catalog title "nat.injective_plus_r"): for every
  natural number n, addition of n on the left is injective in its right
  argument. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_injective_plus_r :
  forall n x y : nat,
    Nat.add n x = Nat.add n y ->
    x = y.
Admitted.
