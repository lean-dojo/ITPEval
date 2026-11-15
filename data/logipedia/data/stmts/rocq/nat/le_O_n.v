(*
  Statement-only formalization of Logipedia corpus artifact nat.le_O_n
  (catalog title "nat.le_O_n"): zero is less than or equal to every natural
  number. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_O_n :
  forall n : nat,
    O <= n.
Admitted.
