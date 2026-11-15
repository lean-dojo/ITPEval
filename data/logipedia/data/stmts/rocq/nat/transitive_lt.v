(*
  Statement-only formalization of Logipedia corpus artifact nat.transitive_lt
  (catalog title "nat.transitive_lt"): the strict order on natural numbers is
  transitive. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_transitive_lt :
  forall a b c : nat,
    Nat.lt a b ->
    Nat.lt b c ->
    Nat.lt a c.
Admitted.
