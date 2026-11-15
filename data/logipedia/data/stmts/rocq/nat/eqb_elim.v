(*
  Statement-only formalization of Logipedia corpus artifact nat.eqb_elim
  (catalog title "nat.eqb_elim"): elimination for natural-number Boolean
  equality, using equality and disequality branches to establish a predicate
  of the equality-test result. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_eqb_elim :
  forall (n m : nat) (P : bool -> Prop),
    (n = m -> P true) ->
    (~ (n = m) -> P false) ->
    P (Nat.eqb n m).
Admitted.
