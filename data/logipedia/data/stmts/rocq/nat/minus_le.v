(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_le
  (catalog title "nat.minus_le"): subtracting any natural number from another
  yields a result no greater than the original minuend. This file contains no
  proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_minus_le :
  forall x y : nat,
    Nat.sub x y <= x.
Admitted.
