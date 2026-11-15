(*
  Statement-only formalization of Logipedia corpus artifact nat.not_le_Sn_O
  (catalog title "nat.not_le_Sn_O"): no successor natural number is less than
  or equal to zero. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_not_le_Sn_O :
  forall n : nat,
    ~ (S n <= O).
Admitted.
