(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_lt_plus_l (catalog title "nat.monotonic_lt_plus_l"):
  adding a fixed natural number on the right is monotone with respect to
  strict less-than. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_monotonic_lt_plus_l :
  forall n x y : nat,
    Nat.lt x y ->
    Nat.lt (Nat.add x n) (Nat.add y n).
Admitted.
