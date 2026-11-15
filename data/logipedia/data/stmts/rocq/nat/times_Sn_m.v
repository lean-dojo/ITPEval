(*
  Statement-only formalization of Logipedia corpus artifact nat.times_Sn_m
  (catalog title "nat.times_Sn_m"): for all natural numbers n and m, m plus
  the product of n and m equals the product of the successor of n and m.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_times_Sn_m :
  forall n m : nat,
    Nat.add m (Nat.mul n m) = Nat.mul (S n) m.
Admitted.
