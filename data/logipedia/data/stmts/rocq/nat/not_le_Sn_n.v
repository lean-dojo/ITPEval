(*
  Statement-only formalization of Logipedia corpus artifact nat.not_le_Sn_n
  (catalog title "nat.not_le_Sn_n"): the successor of every natural number
  is not less than or equal to that number. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_not_le_Sn_n :
  forall n : nat,
    ~ (S n <= n).
Admitted.
