(*
  Statement-only formalization of Logipedia corpus artifact
  nat.not_eq_to_le_to_lt (catalog title "nat.not_eq_to_le_to_lt"): two
  distinct natural numbers in non-strict increasing order are in strict
  increasing order. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_not_eq_to_le_to_lt :
  forall n m : nat,
    n <> m ->
    n <= m ->
    n < m.
Admitted.
