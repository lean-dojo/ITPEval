(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_b6:
  the iterated real series over positive k and nonnegative n with terms
  ((-1)^(k-1) / k) / (k * 2^n + 1) converges to 1. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory seqTheory;

val putnam_2016_b6 =
  ``?inner : num -> real.
      (!k : num.
         (\n : num.
            1 / (&(k + 1) * (2 : real) pow n + 1))
           sums inner k) /\
      (\k : num.
         (-1 : real) pow k / &(k + 1) * inner k)
        sums 1``;
