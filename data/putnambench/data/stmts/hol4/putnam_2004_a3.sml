(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_a3:
  a real sequence whose consecutive two-by-two determinants equal factorials
  and whose first three terms are one has only integer values. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory realTheory intrealTheory;

val putnam_2004_a3 =
  ``!u : num -> real.
      u 0 = 1 /\
      u 1 = 1 /\
      u 2 = 1 /\
      (!n : num.
         u n * u (n + 3) - u (n + 1) * u (n + 2) =
           &(FACT n))
      ==>
      !n : num.
        ?m : int.
          u n = real_of_int m``;
