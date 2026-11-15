(*
  Statement-only formalization of Logipedia corpus artifact nat.plus_n_Sm
  (catalog title "nat.plus_n_Sm"): for all natural numbers n and m, the
  successor of their sum equals n plus the successor of m. This file contains
  no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_plus_n_Sm :
  forall n m : nat,
    S (Nat.add n m) = Nat.add n (S m).
Admitted.
