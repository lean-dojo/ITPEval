(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_S_S
  (catalog title "nat.minus_S_S"): natural-number subtraction cancels one
  successor from both arguments. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_minus_S_S :
  forall n m : nat,
    Nat.sub (S n) (S m) = Nat.sub n m.
Admitted.
