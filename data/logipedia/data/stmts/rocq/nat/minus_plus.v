(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_plus
  (catalog title "nat.minus_plus"): successive truncated subtraction of two
  natural numbers equals subtraction of their sum. This file contains no
  proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_minus_plus :
  forall n m p : nat,
    Nat.sub (Nat.sub n m) p = Nat.sub n (Nat.add m p).
Admitted.
