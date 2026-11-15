(*
  Statement-only formalization of miniF2F valid problem aimeII_2020_p6: a rational recurrence
  whose 2020th term has reduced denominator plus numerator equal to 626. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory ratTheory;

val aimeII_2020_p6 =
  ``!t : num -> rat.
      (t 1 = 20 /\
       t 2 = 21 /\
       (!n : num.
          3 <= n ==>
          t n = (5 * t (n - 1) + 1) / (25 * t (n - 2))))
      ==>
      &(RATD (t 2020)) + RATN (t 2020) = 626``;
