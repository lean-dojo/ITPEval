(*
  Statement-only formalization of Logipedia corpus artifact nat.le_plus_n_r
  (catalog title "nat.le_plus_n_r"): every natural number is less than or
  equal to itself plus another natural number. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_plus_n_r :
  forall n m : nat,
    m <= Nat.add m n.
Admitted.
