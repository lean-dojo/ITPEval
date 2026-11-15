(*
  Statement-only formalization of Logipedia corpus artifact nat.le_n_O_to_eq
  (catalog title "nat.le_n_O_to_eq"): every natural number less than or equal
  to zero is equal to zero. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_n_O_to_eq :
  forall n : nat,
    n <= 0 -> 0 = n.
Admitted.
