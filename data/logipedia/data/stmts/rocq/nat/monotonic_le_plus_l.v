(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_le_plus_l (catalog title "nat.monotonic_le_plus_l"):
  adding a fixed natural number on the right is monotone with respect to
  less-than-or-equal. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_monotonic_le_plus_l :
  forall m x y : nat,
    Nat.le x y ->
    Nat.le (Nat.add x m) (Nat.add y m).
Admitted.
