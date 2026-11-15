(*
  Statement-only formalization of Logipedia corpus artifact nat.plus_n_O
  (catalog title "nat.plus_n_O"): every natural number equals itself plus
  zero on the right. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_plus_n_O :
  forall n : nat,
    n = Nat.add n O.
Admitted.
