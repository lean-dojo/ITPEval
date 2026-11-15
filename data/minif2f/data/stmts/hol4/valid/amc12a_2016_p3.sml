(*
  Statement-only formalization of miniF2F valid problem amc12a_2016_p3: evaluating a real
  remainder function defined using the integer floor. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory;

val amc12a_2016_p3 =
  ``!f : real -> real -> real.
      (!x y.
         y <> 0 ==>
         f x y = x - y * real_of_int (INT_FLOOR (x / y)))
      ==>
      f (3 / 8) (-(2 / 5)) = -(1 / 40)``;
