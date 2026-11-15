(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2013_b2:
  nonnegative finite cosine polynomials whose coefficients at multiples of
  three vanish have attained maximum value 3 at zero. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory transcTheory;

val putnam_2013_b2 =
  ``let C =
      \f : real -> real.
        ?N : num.
          1 <= N /\
          ?a : num -> real.
            (!n : num.
               1 <= n /\ n <= N /\ divides 3 n
               ==>
               a n = 0) /\
            (!x : real. 0 <= f x) /\
            (!x : real.
               f x =
                 1 +
                 SIGMA
                   (\n : num.
                      a n * cos (2 * pi * (&n : real) * x))
                   (IMAGE SUC (count N)))
    in
    let solution = (3 : real)
    in
      (!f : real -> real. C f ==> f 0 <= solution) /\
      (?f : real -> real. C f /\ f 0 = solution)``;
