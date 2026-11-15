(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_plus_to_minus_r (catalog title "nat.le_plus_to_minus_r"): if the sum
  of two natural numbers is at most a third, then the first is at most the
  third minus the second. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_plus_to_minus_r :
  forall a b c : nat,
    Nat.add a b <= c ->
    a <= Nat.sub c b.
Admitted.
