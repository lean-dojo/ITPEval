(*
  Statement-only formalization of Logipedia corpus artifact nat.le_ind
  (catalog title "nat.le_ind"): induction over natural numbers at or above
  a fixed lower bound. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_ind :
  forall (n : nat) (Q : nat -> Prop),
    Q n ->
    (forall m : nat, n <= m -> Q m -> Q (S m)) ->
    forall m : nat, n <= m -> Q m.
Admitted.
