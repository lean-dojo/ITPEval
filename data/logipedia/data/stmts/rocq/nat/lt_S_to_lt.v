(*
  Statement-only formalization of Logipedia corpus artifact nat.lt_S_to_lt
  (catalog title "nat.lt_S_to_lt"): for all natural numbers n and m, if the
  successor of n is strictly less than m, then n is strictly less than m.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_lt_S_to_lt :
  forall n m : nat,
    S n < m ->
    n < m.
Admitted.
