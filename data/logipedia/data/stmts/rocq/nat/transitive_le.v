(*
  Statement-only formalization of Logipedia corpus artifact nat.transitive_le
  (catalog title "nat.transitive_le"): the natural-number less-than-or-equal
  relation is transitive. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_transitive_le :
  forall a b c : nat,
    a <= b ->
    b <= c ->
    a <= c.
Admitted.
