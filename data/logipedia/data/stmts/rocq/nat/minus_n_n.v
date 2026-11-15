(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_n_n
  (catalog title "nat.minus_n_n"): subtracting a natural number from itself
  yields zero. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_minus_n_n :
  forall n : nat,
    O = Nat.sub n n.
Admitted.
