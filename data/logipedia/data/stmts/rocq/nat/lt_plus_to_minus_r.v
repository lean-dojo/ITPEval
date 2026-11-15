(*
  Statement-only formalization of Logipedia corpus artifact
  nat.lt_plus_to_minus_r (catalog title "nat.lt_plus_to_minus_r"): if the sum
  of two natural numbers is strictly less than a third, then the first is
  strictly less than the third minus the second. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_lt_plus_to_minus_r :
  forall a b c : nat,
    Nat.lt (Nat.add a b) c ->
    Nat.lt a (Nat.sub c b).
Admitted.
