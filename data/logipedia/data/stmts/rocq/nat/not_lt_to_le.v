(*
  Statement-only formalization of Logipedia corpus artifact nat.not_lt_to_le
  (catalog title "nat.not_lt_to_le"): for natural numbers, if n is not less
  than m, then m is less than or equal to n. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_not_lt_to_le :
  forall n m : nat,
    ~ Nat.lt n m ->
    Nat.le m n.
Admitted.
