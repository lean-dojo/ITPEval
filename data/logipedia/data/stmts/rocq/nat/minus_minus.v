(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_minus
  (catalog title "nat.minus_minus"): for natural numbers p <= m <= n, adding
  p to the truncated difference n minus m equals n minus the truncated
  difference m minus p. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_minus_minus :
  forall n m p : nat,
    p <= m ->
    m <= n ->
    Nat.add p (Nat.sub n m) = Nat.sub n (Nat.sub m p).
Admitted.
