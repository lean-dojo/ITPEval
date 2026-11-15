(*
  Statement-only formalization of Logipedia corpus artifact nat.times_times
  (catalog title "nat.times_times"): interchanging the first two factors in
  a nested product of natural numbers preserves the result. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_times_times :
  forall x y z : nat,
    Nat.mul x (Nat.mul y z) = Nat.mul y (Nat.mul x z).
Admitted.
