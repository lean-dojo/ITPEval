(*
  Statement-only formalization of miniF2F test problem amc12_2000_p1:
  three pairwise-distinct natural-number factors with product 2001 have sum
  at most 671. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val amc12_2000_p1 =
  ``!i m n : num.
      ~(i = m) /\ ~(m = n) /\ ~(n = i) /\
      (i * m * n = 2001)
      ==>
      (i + m + n <= 671)``;
