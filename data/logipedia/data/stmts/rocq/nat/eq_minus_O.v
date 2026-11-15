(*
  Statement-only formalization of Logipedia corpus artifact nat.eq_minus_O
  (catalog title "nat.eq_minus_O"): if a natural number is at most another,
  subtracting the latter from the former yields zero. This file contains no
  proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_eq_minus_O :
  forall n m : nat,
    n <= m ->
    Nat.sub n m = 0.
Admitted.
