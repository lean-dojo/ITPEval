(*
  Statement-only formalization of Logipedia corpus artifact nat.le_S_S
  (catalog title "nat.le_S_S"): successor preserves less-than-or-equal on
  natural numbers. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_S_S :
  forall n m : nat,
    n <= m ->
    S n <= S m.
Admitted.
