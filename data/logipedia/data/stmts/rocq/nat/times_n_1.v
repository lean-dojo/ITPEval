(*
  Statement-only formalization of Logipedia corpus artifact nat.times_n_1
  (catalog title "nat.times_n_1"): every natural number equals its product
  with one on the right. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_times_n_1 :
  forall n : nat,
    n = Nat.mul n (S O).
Admitted.
