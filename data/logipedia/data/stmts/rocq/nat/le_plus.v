(*
  Statement-only formalization of Logipedia corpus artifact nat.le_plus
  (catalog title "nat.le_plus"): natural-number addition preserves the
  less-than-or-equal relation in both arguments. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_plus :
  forall n1 n2 m1 m2 : nat,
    n1 <= n2 ->
    m1 <= m2 ->
    Nat.add n1 m1 <= Nat.add n2 m2.
Admitted.
