(*
  Statement-only formalization of Logipedia corpus artifact nat.le_plus_to_le
  (catalog title "nat.le_plus_to_le"): cancellation of a common left addend
  from a less-than-or-equal relation on natural numbers. This file contains
  no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_plus_to_le :
  forall a n m : nat,
    Nat.add a n <= Nat.add a m ->
    n <= m.
Admitted.
