(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_a4:
  the iterated real series with terms
  m^2*n / (3^m*(n*3^m + m*3^n)) equals 9/32. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory seqTheory;

val putnam_1999_a4 =
  ``suminf
      (\m : num.
         suminf
           (\n : num.
              ((&(m + 1) : real) pow 2 * &(n + 1)) /
              ((3 : real) pow (m + 1) *
               (&(n + 1) * (3 : real) pow (m + 1) +
                &(m + 1) * (3 : real) pow (n + 1))))) =
    9 / 32``;
