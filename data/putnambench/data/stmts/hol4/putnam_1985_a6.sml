(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1985_a6:
  a real polynomial with constant term one whose positive integer powers have
  the same sum of squared coefficients as those of 3x^2 + 7x + 2. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory realTheory polyTheory;

val putnam_1985_a6 =
  ``!(Gamma : real list -> real) (f : real list).
      Gamma =
        (\p : real list.
           FOLDR (\a acc. a pow 2 + acc) 0 p) /\
      f = [2; 7; 3]
      ==>
      let g = ([1; 5; 6] : real list)
      in
        poly g 0 = 1 /\
        !n : num.
          1 <= n
          ==>
          Gamma (f poly_exp n) = Gamma (g poly_exp n)``;
