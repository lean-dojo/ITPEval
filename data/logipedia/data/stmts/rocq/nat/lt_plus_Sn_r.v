(*
  Statement-only formalization of Logipedia corpus artifact nat.lt_plus_Sn_r
  (catalog title "nat.lt_plus_Sn_r"): every natural number a is strictly less
  than (a + x) + (n + 1) for all natural numbers x and n. This file contains
  no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_lt_plus_Sn_r :
  forall a x n : nat,
    a < Nat.add (Nat.add a x) (S n).
Admitted.
