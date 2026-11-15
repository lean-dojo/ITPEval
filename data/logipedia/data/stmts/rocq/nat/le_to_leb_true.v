(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_to_leb_true (catalog title "nat.le_to_leb_true"): if one natural
  number is at most another, their Boolean less-than-or-equal test returns
  true. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_to_leb_true :
  forall n m : nat,
    n <= m ->
    Nat.leb n m = true.
Admitted.
