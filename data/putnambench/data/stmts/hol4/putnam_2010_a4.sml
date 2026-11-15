(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_a4:
  for every positive natural number n, the number
  10^(10^(10^n)) + 10^(10^n) + 10^n - 1 is not prime. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;
open dividesTheory;

val putnam_2010_a4 =
  ``!n : num.
      0 < n ==>
      ~prime
        ((10 : num) EXP (10 EXP (10 EXP n)) +
         10 EXP (10 EXP n) +
         10 EXP n - 1)``;
