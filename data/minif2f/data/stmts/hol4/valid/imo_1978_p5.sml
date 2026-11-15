(*
  Statement-only formalization of miniF2F valid artifact imo_1978_p5: the harmonic-sum
  inequality for an injective natural-number sequence with initial value zero. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val imo_1978_p5 =
  ``!n : num. !a : num -> num.
      (!x y. a x = a y ==> x = y) /\
      a 0 = 0 /\
      0 < n
      ==>
      sum {1 .. n} (\k. (1 : real) / (&k : real)) <=
        sum {1 .. n}
          (\k. (&(a k) : real) / ((&k : real) pow 2))``;
