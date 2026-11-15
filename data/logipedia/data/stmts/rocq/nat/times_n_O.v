(*
  Statement-only formalization of Logipedia corpus artifact nat.times_n_O
  (catalog title "nat.times_n_O"): for every natural number, zero equals that
  number multiplied by zero on the right. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_times_n_O :
  forall n : nat,
    O = Nat.mul n O.
Admitted.
