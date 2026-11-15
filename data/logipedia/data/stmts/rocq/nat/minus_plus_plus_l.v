(*
  Statement-only formalization of Logipedia corpus artifact
  nat.minus_plus_plus_l (catalog title "nat.minus_plus_plus_l"): adding the
  same natural number to both operands preserves truncated subtraction. This
  file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_minus_plus_plus_l :
  forall x y h : nat,
    Nat.sub (Nat.add x h) (Nat.add y h) = Nat.sub x y.
Admitted.
