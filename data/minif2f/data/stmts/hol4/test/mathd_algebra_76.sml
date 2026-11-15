(*
  Statement-only formalization of miniF2F test problem mathd_algebra_76: an integer function
  given by separate quadratic formulas on odd and even inputs evaluates to -1 at 4. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val mathd_algebra_76 =
  ``!f : int -> int.
      (!n : int.
         (?k : int. n = 2 * k + 1)
         ==>
         f n = n ** 2) /\
      (!n : int.
         (?k : int. n = 2 * k)
         ==>
         f n = n ** 2 - 4 * n - 1)
      ==>
      f 4 = ~1``;
