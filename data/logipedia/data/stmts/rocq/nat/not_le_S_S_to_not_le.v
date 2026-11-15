(*
  Statement-only formalization of Logipedia corpus artifact
  nat.not_le_S_S_to_not_le (catalog title "nat.not_le_S_S_to_not_le"):
  for all natural numbers n and m, if the successor of n is not less than
  or equal to the successor of m, then n is not less than or equal to m.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_not_le_S_S_to_not_le :
  forall n m : nat,
    ~ (S n <= S m) ->
    ~ (n <= m).
Admitted.
