(*
  Statement-only formalization of PutnamBench artifact putnam_1978_b2:
  the iterated real series over positive integers with terms
  1 / (i^2*j + 2*i*j + i*j^2) equals 7/4. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory seqTheory;

val putnam_1978_b2 =
  ``suminf
      (\i : num.
         suminf
           (\j : num.
              1 /
              ((&(i + 1) : real) pow 2 * &(j + 1) +
               2 * &(i + 1) * &(j + 1) +
               &(i + 1) * (&(j + 1) pow 2)))) =
    7 / 4``;
