(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_plus_to_le_r (catalog title "nat.le_plus_to_le_r"): cancellation of
  a common right addend from a less-than-or-equal relation on natural numbers.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_plus_to_le_r :
  forall a n m : nat,
    Nat.add n a <= Nat.add m a ->
    n <= m.
Admitted.
