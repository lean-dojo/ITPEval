(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1986_a3:
  the series of principal arccot values at n^2 + n + 1 equals pi / 2.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory seqTheory transcTheory;

val putnam_1986_a3 =
  ``!cot : real -> real. !arccot : real -> real.
      (!x : real. cot x = cos x / sin x) /\
      (!t : real.
         0 <= t
         ==>
         0 < arccot t /\
         arccot t <= pi / 2 /\
         cot (arccot t) = t)
      ==>
      suminf
        (\n : num.
           arccot ((&n : real) pow 2 + &n + 1)) =
      pi / 2``;
