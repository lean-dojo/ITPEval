(*
  Statement-only formalization of Logipedia corpus artifact nat.eqb_n_n
  (catalog title "nat.eqb_n_n"): the Boolean equality test of any natural
  number with itself is true. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_eqb_n_n :
  forall n : nat,
    Nat.eqb n n = true.
Admitted.
