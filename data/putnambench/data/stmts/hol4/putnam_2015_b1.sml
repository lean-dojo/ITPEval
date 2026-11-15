(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_b1:
  a three-times differentiable real function with at least five distinct real
  zeros has at least two distinct real zeros of
  f + 6 f' + 12 f'' + 8 f'''. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory limTheory;

val putnam_2015_b1 =
  ``!f : real -> real.
      (!x : real. higher_differentiable 3 f x) /\
      (?z : num -> real.
         (!i : num.
            i < 5
            ==>
            f (z i) = 0) /\
         (!i j : num.
            i < 5 /\ j < 5 /\ z i = z j
            ==>
            i = j))
      ==>
      ?x y : real.
        x <> y /\
        f x + 6 * diffn 1 f x + 12 * diffn 2 f x +
          8 * diffn 3 f x = 0 /\
        f y + 6 * diffn 1 f y + 12 * diffn 2 f y +
          8 * diffn 3 f y = 0``;
