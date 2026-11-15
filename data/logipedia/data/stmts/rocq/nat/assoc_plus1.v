(*
  Statement-only formalization of Logipedia corpus artifact nat.assoc_plus1
  (catalog title "nat.assoc_plus1"): a reassociation identity for addition of
  three natural numbers. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_assoc_plus1 :
  forall a b c : nat,
    Nat.add c (Nat.add b a) = Nat.add (Nat.add b c) a.
Admitted.
