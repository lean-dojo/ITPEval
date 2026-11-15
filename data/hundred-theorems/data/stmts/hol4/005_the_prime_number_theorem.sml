(*
  Statement-only formalization of "The Prime Number Theorem" from Hundred Theorems item 005.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory realTheory transcTheory;
open real_topologyTheory;

val prime_number_theorem =
  ``((\(k : num).
        &(CARD {p : num | prime p /\ p <= k}) /
        ((&k : real) / ln (&k))) --> (1 : real)) sequentially``;
