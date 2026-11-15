(*
  Statement-only formalization of Logipedia corpus artifact
  nat.minus_to_plus (catalog title "nat.minus_to_plus"): if m is at most n
  and n minus m equals p, then n equals m plus p. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_minus_to_plus :
  forall n m p : nat,
    Nat.le m n ->
    Nat.sub n m = p ->
    n = Nat.add m p.
Admitted.
