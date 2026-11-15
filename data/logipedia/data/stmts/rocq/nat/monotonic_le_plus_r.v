(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_le_plus_r (catalog title "nat.monotonic_le_plus_r"):
  adding a fixed natural number on the left is monotone with respect to
  less-than-or-equal. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_monotonic_le_plus_r :
  forall n a b : nat,
    Nat.le a b ->
    Nat.le (Nat.add n a) (Nat.add n b).
Admitted.
