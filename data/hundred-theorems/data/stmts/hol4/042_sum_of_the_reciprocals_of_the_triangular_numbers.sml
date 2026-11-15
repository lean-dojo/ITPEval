(*
  Statement-only formalization of "Sum of the Reciprocals of the Triangular Numbers" from
  Hundred Theorems item 042. The partial sums of the reciprocals of the nonzero triangular
  numbers converge to 2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val sum_of_the_reciprocals_of_the_triangular_numbers =
  ``!e : real.
      0 < e
      ==>
      ?N : num.
        !n : num.
          N <= n
          ==>
          abs
            (SIGMA
               (\k : num.
                  (1 : real) /
                  &((k * (k + 1)) DIV 2))
               (IMAGE SUC (count n)) -
             2) < e``;
