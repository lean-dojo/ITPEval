(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_b1:
  every coefficient in the real power series of the exponential of an
  integer polynomial with zero constant term and odd linear coefficient is
  nonzero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory realTheory intrealTheory
     polyTheory seqTheory transcTheory;

val putnam_2022_b1 =
  ``!P : int list. !b : num -> real.
      1 < LENGTH P /\
      EL 0 P = 0 /\
      ODD (Num (ABS (EL 1 P))) /\
      (!x : real.
         (\k : num. b k * x pow k) sums
           exp (poly (MAP real_of_int P) x))
      ==>
      !k : num. b k <> 0``;
