(*
  Statement-only formalization of miniF2F valid problem amc12_2000_p15: a complex functional
  equation determining the sum of the scaled preimages of 7. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory complexTheory;

val amc12_2000_p15 =
  ``!f : complex -> complex.
      (!x : complex. f (x / 3) = x pow 2 + x + 1) /\
      FINITE {y : complex | f y = 7}
      ==>
      ITSET
        (\y acc. y / 3 + acc)
        {y : complex | f y = 7}
        0 = ~(1 / 9)``;
