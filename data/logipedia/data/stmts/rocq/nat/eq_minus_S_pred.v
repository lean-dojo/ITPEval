(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_minus_S_pred (catalog title "nat.eq_minus_S_pred"):
  subtracting a successor from a natural number equals the predecessor of
  subtracting its predecessor. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_eq_minus_S_pred :
  forall n m : nat,
    Nat.sub n (S m) = Nat.pred (Nat.sub n m).
Admitted.
