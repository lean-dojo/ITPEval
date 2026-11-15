(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_b1:
  positive integers h and k admit positive integers m and n for every positive
  real epsilon such that |h * sqrt m - k * sqrt n| lies strictly between
  epsilon and 2 * epsilon. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory transcTheory;

val putnam_2011_b1 =
  ``!h k : num.
      0 < h /\ 0 < k
      ==>
      !epsilon : real.
        0 < epsilon
        ==>
        ?m n : num.
          0 < m /\
          0 < n /\
          epsilon <
            abs
              ((&h : real) * sqrt (&m : real) -
               (&k : real) * sqrt (&n : real)) /\
          abs
              ((&h : real) * sqrt (&m : real) -
               (&k : real) * sqrt (&n : real)) <
            2 * epsilon``;
