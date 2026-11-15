(*
  Statement-only formalization of Logipedia corpus artifact nat.le_plus_n
  (catalog title "nat.le_plus_n"): for all natural numbers n and m, m is
  less than or equal to n plus m. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_plus_n :
  forall n m : nat,
    m <= Nat.add n m.
Admitted.
