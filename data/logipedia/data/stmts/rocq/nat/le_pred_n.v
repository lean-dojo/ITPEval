(*
  Statement-only formalization of Logipedia corpus artifact nat.le_pred_n
  (catalog title "nat.le_pred_n"): the predecessor of every natural number
  is less than or equal to that number. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_pred_n :
  forall n : nat,
    Nat.pred n <= n.
Admitted.
