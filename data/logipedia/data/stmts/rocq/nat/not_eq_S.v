(*
  Statement-only formalization of Logipedia corpus artifact nat.not_eq_S
  (catalog title "nat.not_eq_S"): distinct natural numbers have distinct
  successors. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_not_eq_S :
  forall n m : nat,
    n <> m ->
    S n <> S m.
Admitted.
