(*
  Statement-only formalization of Logipedia corpus artifact nat.lt_O_n_elim
  (catalog title "nat.lt_O_n_elim"): every positive natural number satisfies
  any predicate that holds for every successor. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_lt_O_n_elim :
  forall n : nat,
    O < n ->
    forall P : nat -> Prop,
      (forall m : nat, P (S m)) ->
      P n.
Admitted.
