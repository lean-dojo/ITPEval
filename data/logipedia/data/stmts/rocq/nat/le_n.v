(*
  Statement-only formalization of Logipedia corpus artifact nat.le_n
  (catalog title "nat.le_n"): the natural-number less-than-or-equal relation
  is reflexive. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_n :
  forall n : nat,
    n <= n.
Admitted.
