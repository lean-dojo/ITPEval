(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1990_b5:
  existence of a nonzero real coefficient sequence whose degree-n
  truncation has exactly n distinct real roots for every positive n.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_1990_b5 =
  ``let real_roots =
      \a : num -> real.
      \n : num.
        {x : real |
           SIGMA
             (\i : num. a i * x pow i)
             (count (n + 1)) =
           0}
    in
    let putnam_1990_b5_solution = T
    in
      ((?a : num -> real.
          (!i : num. a i <> 0) /\
          (!n : num.
             1 <= n
             ==>
             FINITE (real_roots a n) /\
             CARD (real_roots a n) = n))
       <=>
       putnam_1990_b5_solution)``;
