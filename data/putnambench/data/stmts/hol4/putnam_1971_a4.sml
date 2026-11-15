(*
  Statement-only formalization of PutnamBench artifact putnam_1971_a4:
  eventual strict positivity of every coefficient in the finite homogeneous
  support of a parameterized bivariate polynomial. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory realTheory;

val putnam_1971_a4 =
  ``let coeff =
      \n : num. \epsilon : real. \i j : num.
        if i + j = n + 2 then
          (if 2 <= i then (&(binomial n (i - 2)) : real) else 0) -
          (2 - epsilon) *
            (if 1 <= i then (&(binomial n (i - 1)) : real) else 0) +
          (&(binomial n i) : real)
        else
          0
    in
      !epsilon : real.
        0 < epsilon /\ epsilon < 1
        ==>
        ?N : num.
          !n : num.
            N <= n
            ==>
            !i : num.
              i <= n + 2
              ==>
              0 < coeff n epsilon i (n + 2 - i)``;
