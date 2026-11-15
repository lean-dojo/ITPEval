(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1986_a6:
  the value at one of a real polynomial satisfying the given sparse
  polynomial identity is the product of its distinct positive exponents
  divided by n factorial. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory listTheory pred_setTheory realTheory
     real_sigmaTheory polyTheory;

val putnam_1986_a6 =
  ``!n : num. !a : num -> real. !b : num -> num. !f : real list.
      0 < n /\
      (!i : num.
         i IN IMAGE SUC (count n)
         ==>
         0 < b i) /\
      (!i j : num.
         i IN IMAGE SUC (count n) /\
         j IN IMAGE SUC (count n) /\
         b i = b j
         ==>
         i = j) /\
      (!x : real.
         (1 - x) pow n * poly f x =
           1 +
           SIGMA
             (\i : num. a i * x pow (b i))
             (IMAGE SUC (count n)))
      ==>
      poly f 1 =
        REAL_PROD_IMAGE
          (\i : num. &(b i))
          (IMAGE SUC (count n)) /
        &(FACT n)``;
