(*
  Statement-only formalization of Logipedia corpus artifact
  cong.let_clause_73 (catalog title "cong.let_clause_73"):
  swapping the first two summands preserves a right-associated sum of
  natural numbers, under the source theorem's quantified context.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem cong_let_clause_73 :
  forall n m p : nat,
    0 < p ->
    forall x134 x135 x136 : nat,
      x134 + (x135 + x136) = x135 + (x134 + x136).
Admitted.
