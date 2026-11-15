(*
  Statement-only formalization of Logipedia corpus artifact nat.ltn_to_ltO
  (catalog title "nat.ltn_to_ltO"): for all natural numbers n and m, if n is
  strictly less than m, then zero is strictly less than m. This file contains
  no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_ltn_to_ltO :
  forall n m : nat,
    Nat.lt n m ->
    Nat.lt O m.
Admitted.
