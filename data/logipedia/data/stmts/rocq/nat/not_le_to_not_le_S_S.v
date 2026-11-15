(*
  Statement-only formalization of Logipedia corpus artifact
  nat.not_le_to_not_le_S_S (catalog title "nat.not_le_to_not_le_S_S"):
  for all natural numbers n and m, if n is not less than or equal to m,
  then the successor of n is not less than or equal to the successor of m.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_not_le_to_not_le_S_S :
  forall n m : nat,
    ~ (n <= m) ->
    ~ (S n <= S m).
Admitted.
