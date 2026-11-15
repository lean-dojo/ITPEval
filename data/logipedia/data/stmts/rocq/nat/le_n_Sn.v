(*
  Statement-only formalization of Logipedia corpus artifact nat.le_n_Sn
  (catalog title "nat.le_n_Sn"): every natural number is less than or equal
  to its successor. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_n_Sn :
  forall n : nat,
    n <= S n.
Admitted.
