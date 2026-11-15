(*
  Statement-only formalization of PutnamBench artifact putnam_1971_a2:
  the real polynomials satisfying P(0) = 0 and
  P(x^2 + 1) = P(x)^2 + 1 are exactly the identity polynomial.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open listTheory realTheory polyTheory;

val putnam_1971_a2 =
  ``!P : real list.
      (poly P 0 = 0 /\
       (!x : real.
          poly P (x pow 2 + 1) = (poly P x) pow 2 + 1))
      <=>
      (!x : real. poly P x = x)``;
