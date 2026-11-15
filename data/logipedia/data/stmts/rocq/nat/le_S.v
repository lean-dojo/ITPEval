(*
  Statement-only formalization of Logipedia corpus artifact nat.le_S
  (catalog title "nat.le_S"): for all natural numbers n and m, if n is
  less than or equal to m, then n is less than or equal to the successor
  of m. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_S :
  forall n m : nat,
    n <= m ->
    n <= S m.
Admitted.
