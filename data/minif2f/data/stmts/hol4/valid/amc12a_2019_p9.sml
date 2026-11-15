(*
  Statement-only formalization of miniF2F valid problem amc12a_2019_p9: a rational sequence
  defined by two initial values and a recurrence has reduced numerator plus denominator 8078
  at index 2019. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory ratTheory;

val _ = new_theory "hello";

val amc12a_2019_p9 =
  ``!a : num -> rat.
      (a 1 = 1 /\
       a 2 = 3 / 7 /\
       (!n : num.
          a (n + 2) =
            a n * a (n + 1) / (2 * a n - a (n + 1))))
      ==>
      RATN (a 2019) + &(RATD (a 2019)) = 8078``;

val _ = export_theory();
