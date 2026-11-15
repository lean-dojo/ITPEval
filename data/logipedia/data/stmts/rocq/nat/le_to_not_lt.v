(*
  Statement-only formalization of Logipedia corpus artifact nat.le_to_not_lt
  (catalog title "nat.le_to_not_lt"): for all natural numbers n and m, if n
  is less than or equal to m, then m is not strictly less than n. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_to_not_lt :
  forall n m : nat,
    n <= m ->
    ~ (m < n).
Admitted.
