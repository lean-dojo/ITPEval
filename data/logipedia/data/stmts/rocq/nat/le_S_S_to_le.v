(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_S_S_to_le (catalog title "nat.le_S_S_to_le"): for all natural
  numbers n and m, if the successor of n is less than or equal to the
  successor of m, then n is less than or equal to m. This file contains no
  proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_S_S_to_le :
  forall n m : nat,
    S n <= S m ->
    n <= m.
Admitted.
