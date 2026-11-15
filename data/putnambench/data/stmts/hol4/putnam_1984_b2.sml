(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1984_b2:
  the minimum value is 8 for the stated sum of two squared real expressions
  over 0 < u < sqrt 2 and v > 0. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val putnam_1984_b2 =
  ``let objective =
      \u v : real.
        (u - v) pow 2 + (sqrt (2 - u pow 2) - 9 / v) pow 2
    in
      (!u v : real.
         0 < u /\ u < sqrt 2 /\ 0 < v
         ==>
         8 <= objective u v) /\
      (?u v : real.
         0 < u /\ u < sqrt 2 /\ 0 < v /\
         objective u v = 8)``;
