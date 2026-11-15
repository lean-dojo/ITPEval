(*
  Statement-only formalization of PutnamBench artifact putnam_1972_a5:
  nondivisibility of 2^n - 1 by every natural number n greater than one.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val putnam_1972_a5 =
  ``!n : num.
      1 < n
      ==>
      ~(divides n (2 EXP n - 1))``;
