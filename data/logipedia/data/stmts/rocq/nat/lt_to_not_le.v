(*
  Statement-only formalization of Logipedia corpus artifact nat.lt_to_not_le
  (catalog title "nat.lt_to_not_le"): a strict natural-number inequality
  n < m implies that m is not less than or equal to n. This file contains no
  proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_lt_to_not_le :
  forall n m : nat,
    Nat.lt n m ->
    ~ Nat.le m n.
Admitted.
