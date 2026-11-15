(*
  Statement-only formalization of Logipedia corpus artifact nat.decidable_le
  (catalog title "nat.decidable_le"): natural-number less-than-or-equal is
  decidable for every pair of natural numbers. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_decidable_le :
  forall n m : nat,
    (n <= m) \/ ~ (n <= m).
Admitted.
