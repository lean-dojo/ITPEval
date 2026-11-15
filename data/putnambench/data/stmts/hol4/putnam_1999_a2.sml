(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_a2:
  every real polynomial that is nonnegative on the real line is a finite
  nonempty sum of squares of real polynomials. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory polyTheory;

val putnam_1999_a2 =
  ``!p : real list.
      (!x : real. 0 <= poly p x)
      ==>
      ?k : num. ?f : num -> real list.
        0 < k /\
        !x : real.
          poly p x =
            SIGMA
              (\j : num. (poly (f j) x) pow 2)
              (count k)``;
