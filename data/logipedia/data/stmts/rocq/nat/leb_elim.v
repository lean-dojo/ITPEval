(*
  Statement-only formalization of Logipedia corpus artifact nat.leb_elim
  (catalog title "nat.leb_elim"): elimination for natural-number Boolean
  less-than-or-equal, using order and non-order branches to establish a
  predicate of the comparison result. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_leb_elim :
  forall (n m : nat) (P : bool -> Prop),
    (n <= m -> P true) ->
    (~ (n <= m) -> P false) ->
    P (Nat.leb n m).
Admitted.
