(*
  Statement-only formalization of Logipedia corpus artifact nat.le_plus_b
  (catalog title "nat.le_plus_b"): for natural numbers b, n, and m, if
  n plus b is less than or equal to m, then n is less than or equal to m.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_plus_b :
  forall b n m : nat,
    Nat.add n b <= m ->
    n <= m.
Admitted.
