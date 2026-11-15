(*
  Statement-only formalization of Logipedia corpus artifact
  nat.plus_minus_m_m (catalog title "nat.plus_minus_m_m"): if a natural
  number m is at most n, then adding m to n minus m returns n. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_plus_minus_m_m :
  forall n m : nat,
    Nat.le m n ->
    n = Nat.add (Nat.sub n m) m.
Admitted.
