(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1986_a1:
  the maximum value of x cubed minus 3x over the real numbers satisfying
  x to the fourth plus 36 at most 13x squared is 18. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val putnam_1986_a1 =
  ``let putnam_1986_a1_solution = (18 : real)
    in
    let f = \x : real. x pow 3 - 3 * x
    in
      (!x : real.
         x pow 4 + 36 <= 13 * x pow 2
         ==>
         f x <= putnam_1986_a1_solution) /\
      (?x : real.
         x pow 4 + 36 <= 13 * x pow 2 /\
         f x = putnam_1986_a1_solution)``;
