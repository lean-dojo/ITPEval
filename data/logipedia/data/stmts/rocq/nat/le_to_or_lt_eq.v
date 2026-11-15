(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_to_or_lt_eq (catalog title "nat.le_to_or_lt_eq"): a natural-number
  inequality n <= m implies that either n < m or n = m. This file contains
  no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_to_or_lt_eq :
  forall n m : nat,
    n <= m ->
    n < m \/ n = m.
Admitted.
