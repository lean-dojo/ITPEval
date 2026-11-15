(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1991_b4:
  for an odd prime p, a finite sum of products of binomial coefficients is
  congruent to 2^p + 1 modulo p^2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory pred_setTheory;

val putnam_1991_b4 =
  ``!p : num.
      ODD p /\ prime p
      ==>
      SIGMA
        (\j : num. binomial p j * binomial (p + j) j)
        (count (SUC p)) MOD (p EXP 2) =
      (2 EXP p + 1) MOD (p EXP 2)``;
