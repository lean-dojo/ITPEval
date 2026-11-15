(*
  Statement-only formalization of Logipedia corpus artifact nat.times_O_n
  (catalog title "nat.times_O_n"): multiplying zero on the left by any
  natural number yields zero. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_times_O_n :
  forall n : nat,
    O = Nat.mul O n.
Admitted.
