(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_to_lt_to_lt (catalog title "nat.le_to_lt_to_lt"): natural-number
  order transitivity from n <= m and m < p to n < p. This file contains no
  proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_to_lt_to_lt :
  forall n m p : nat,
    n <= m ->
    m < p ->
    n < p.
Admitted.
