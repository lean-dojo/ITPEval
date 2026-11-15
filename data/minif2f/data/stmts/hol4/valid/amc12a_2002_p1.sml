(*
  Statement-only formalization of miniF2F valid problem amc12a_2002_p1: the sum of the distinct
  complex zeros of a specified polynomial function is 7 / 2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory complexTheory;

val amc12a_2002_p1 =
  ``!f : complex -> complex.
      (!x : complex.
         f x =
           (2 * x + 3) * (x - 4) +
           (2 * x + 3) * (x - 6)) /\
      FINITE {y : complex | f y = 0}
      ==>
      ITSET
        (\y acc. y + acc)
        {y : complex | f y = 0}
        0 = 7 / 2``;
