(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_O_n
  (catalog title "nat.minus_O_n"): subtracting any natural number from zero
  yields zero. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_minus_O_n :
  forall n : nat,
    O = Nat.sub O n.
Admitted.
