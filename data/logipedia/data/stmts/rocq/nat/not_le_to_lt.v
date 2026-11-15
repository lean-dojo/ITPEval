(*
  Statement-only formalization of Logipedia corpus artifact
  nat.not_le_to_lt (catalog title "nat.not_le_to_lt"): if one natural number
  is not less than or equal to another, then the latter is strictly less than
  the former. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_not_le_to_lt :
  forall n m : nat,
    ~ (n <= m) ->
    m < n.
Admitted.
