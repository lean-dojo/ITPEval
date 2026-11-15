(*
  Statement-only formalization of Logipedia corpus artifact nat.S_pred
  (catalog title "nat.S_pred"): every positive natural number is the
  successor of its predecessor. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_S_pred :
  forall n : nat,
    O < n ->
    S (Nat.pred n) = n.
Admitted.
