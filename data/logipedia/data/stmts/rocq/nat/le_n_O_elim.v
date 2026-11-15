(*
  Statement-only formalization of Logipedia corpus artifact nat.le_n_O_elim
  (catalog title "nat.le_n_O_elim"): a natural number less than or equal to
  zero satisfies every predicate that holds at zero. This file contains no
  proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_n_O_elim :
  forall n : nat,
    n <= O ->
    forall P : nat -> Prop,
      P O ->
      P n.
Admitted.
