(*
  Statement-only formalization of Logipedia corpus artifact
  nat.plus_to_minus (catalog title "nat.plus_to_minus"): if a natural number
  n equals m plus p, then subtracting m from n yields p. This file contains no
  proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_plus_to_minus :
  forall n m p : nat,
    n = Nat.add m p ->
    Nat.sub n m = p.
Admitted.
