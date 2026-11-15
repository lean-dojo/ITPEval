(*
  Statement-only formalization of Logipedia corpus artifact nat.pred_Sn
  (catalog title "nat.pred_Sn"): the predecessor of the successor of every
  natural number is that number. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_pred_Sn :
  forall n : nat,
    n = Nat.pred (S n).
Admitted.
