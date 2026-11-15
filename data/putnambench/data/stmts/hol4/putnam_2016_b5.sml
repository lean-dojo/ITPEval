(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_b5:
  the classification of functions from (1, infinity) to itself that preserve
  the interval between the square and cube of each input. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val putnam_2016_b5 =
  ``!f : real -> real.
      ((!x : real. 1 < x ==> 1 < f x) /\
       (!x y : real.
          1 < x /\ 1 < y /\ x pow 2 <= y /\ y <= x pow 3
          ==>
          f x pow 2 <= f y /\ f y <= f x pow 3))
      <=>
      ?c : real.
        0 < c /\
        !x : real.
          1 < x ==> f x = x powr c``;
