(*
  Statement-only formalization of Logipedia corpus artifact
  nat.minus_plus_m_m (catalog title "nat.minus_plus_m_m"): adding a natural
  number m to n and then subtracting m returns n. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_minus_plus_m_m :
  forall n m : nat,
    n = Nat.sub (Nat.add n m) m.
Admitted.
