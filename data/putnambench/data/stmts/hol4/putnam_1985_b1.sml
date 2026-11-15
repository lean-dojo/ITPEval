(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1985_b1:
  the five distinct integers -2, -1, 0, 1, and 2 minimize the number of
  nonzero coefficients in their monic real polynomial among all choices of
  five distinct integer roots. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory intrealTheory listTheory realTheory
     polyTheory;

val putnam_1985_b1 =
  ``let putnam_1985_b1_solution = ([~2; ~1; 0; 1; 2] : int list)
    in
    let factor =
      \m : int. ([~(real_of_int m); 1] : real list)
    in
    let p =
      \m1 m2 m3 m4 m5 : int.
        poly_mul (factor m1)
          (poly_mul (factor m2)
            (poly_mul (factor m3)
              (poly_mul (factor m4) (factor m5))))
    in
    let numnzcoeff =
      \P : real list. LENGTH (FILTER (\c : real. c <> 0) P)
    in
      ALL_DISTINCT putnam_1985_b1_solution /\
      !a b c d e : int.
        ALL_DISTINCT [a; b; c; d; e]
        ==>
        numnzcoeff (p (~2) (~1) 0 1 2) <=
        numnzcoeff (p a b c d e)``;
