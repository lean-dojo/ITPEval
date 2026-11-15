(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_a5:
  every smooth nonnegative real function taking the values zero at zero and
  one at one has a negative derivative of some positive order at some real
  point. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory limTheory;

val putnam_2018_a5 =
  ``!f : real -> real.
      (!n : num. !x : real. higher_differentiable n f x) /\
      f 0 = 0 /\
      f 1 = 1 /\
      (!x : real. 0 <= f x)
      ==>
      ?n : num. ?x : real.
        0 < n /\ diffn n f x < 0``;
