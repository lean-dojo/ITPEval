(*
  Statement-only formalization of Logipedia corpus artifact nat.decidable_lt
  (catalog title "nat.decidable_lt"): natural-number strict less-than is
  decidable for every pair of natural numbers. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_decidable_lt :
  forall n m : nat,
    (n < m) \/ ~ (n < m).
Admitted.
