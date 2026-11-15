(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_plus_minus_m_m (catalog title "nat.le_plus_minus_m_m"): every natural
  number n is at most the sum of its truncated difference n minus m and m.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_plus_minus_m_m :
  forall n m : nat,
    n <= Nat.add (Nat.sub n m) m.
Admitted.
