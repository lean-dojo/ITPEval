(*
  Statement-only formalization of Logipedia corpus artifact nat.plus_minus
  (catalog title "nat.plus_minus"): for natural numbers m at most n, adding p
  to the truncated difference n minus m equals subtracting m from n plus p.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_plus_minus :
  forall m n p : nat,
    Nat.le m n ->
    Nat.add (Nat.sub n m) p = Nat.sub (Nat.add n p) m.
Admitted.
