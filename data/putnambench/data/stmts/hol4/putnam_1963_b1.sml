(*
  Statement-only formalization of PutnamBench artifact putnam_1963_b1:
  the integer parameter for which x^2 - x + a divides x^13 + x + 90 is
  exactly 2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory polyTheory;

val putnam_1963_b1 =
  ``!a : int.
      (([real_of_int a; ~1; 1] : real list) poly_divides
       ([90; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1] : real list))
      <=>
      a = 2``;
