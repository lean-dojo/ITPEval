(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_to_le_to_eq (catalog title "nat.le_to_le_to_eq"): antisymmetry of
  the less-than-or-equal relation on natural numbers. This file contains no
  proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_to_le_to_eq :
  forall n m : nat,
    n <= m ->
    m <= n ->
    n = m.
Admitted.
