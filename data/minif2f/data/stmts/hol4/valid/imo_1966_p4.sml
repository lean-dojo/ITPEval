(*
  Statement-only formalization of miniF2F valid problem imo_1966_p4: a finite
  reciprocal-sine sum identity for real arguments avoiding integer multiples of pi divided
  by powers of two. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory intrealTheory
     real_sigmaTheory transcTheory;

val _ = new_theory "hello";

val imo_1966_p4 =
  ``!n : num. !x : real.
      (!k : num.
         0 < k ==>
         !m : int. x <> real_of_int m * pi / ((2 : real) pow k)) /\
      0 < n
      ==>
      sum {1 .. n} (\k. 1 / sin (((2 : real) pow k) * x)) =
        1 / tan x - 1 / tan (((2 : real) pow n) * x)``;

val _ = export_theory();
