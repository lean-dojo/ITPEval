(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_a1:
  every nonzero Taylor coefficient at zero of (1 - x + x^2) exp(x) is rational
  with reduced numerator equal to one or a prime. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory realTheory limTheory transcTheory ratTheory
     real_of_ratTheory;

val putnam_2014_a1 =
  ``let coefficient =
      \n : num.
        diffn n
          (\x : real. (1 - x + x pow 2) * exp x)
          0 /
        &(FACT n)
    in
      !n : num.
        coefficient n <> 0
        ==>
        ?q : rat.
          coefficient n = real_of_rat q /\
          (RATN q = 1 \/ prime (Num (ABS (RATN q))))``;
