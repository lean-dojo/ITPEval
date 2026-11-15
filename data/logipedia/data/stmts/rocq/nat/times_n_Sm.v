(*
  Statement-only formalization of Logipedia corpus artifact nat.times_n_Sm
  (catalog title "nat.times_n_Sm"): for all natural numbers n and m, n plus
  the product of n and m equals the product of n and the successor of m. This
  file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_times_n_Sm :
  forall n m : nat,
    Nat.add n (Nat.mul n m) = Nat.mul n (S m).
Admitted.
