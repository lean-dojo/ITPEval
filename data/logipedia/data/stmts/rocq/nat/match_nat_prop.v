(*
  Statement-only formalization of Logipedia corpus artifact nat.match_nat_prop
  (catalog title "nat.match_nat_prop"): case elimination for natural numbers,
  from the zero case and all successor cases. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_match_nat_prop :
  forall return_ : nat -> Prop,
    return_ O ->
    (forall n : nat, return_ (S n)) ->
    forall z : nat, return_ z.
Admitted.
