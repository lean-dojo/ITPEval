(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1980_b3:
  the real initial values for which the sequence u_0 = a and
  u_(n+1) = 2 * u_n - n^2 remains positive at every natural index.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val putnam_1980_b3 =
  ``!a : real. !u : num -> real.
      u 0 = a /\
      (!n : num.
         u (n + 1) = 2 * u n - (&n : real) pow 2)
      ==>
      ((!n : num. 0 < u n) <=> 3 <= a)``;
