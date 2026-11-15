(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_n_O
  (catalog title "nat.minus_n_O"): every natural number equals itself after
  subtracting zero. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_minus_n_O :
  forall n : nat,
    n = Nat.sub n O.
Admitted.
