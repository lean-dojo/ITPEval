(*
  Statement-only formalization of PutnamBench artifact putnam_1974_a6:
  the minimum degree of a monic integer polynomial whose value at every
  integer is divisible by 10^6 is 25. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory;

val putnam_1974_a6 =
  ``let eval_int_poly =
      \coeffs x.
        FOLDR (\a acc. a + x * acc) (0 : int) coeffs
    in
    let admissible =
      \coeffs : int list.
        coeffs <> [] /\
        LAST coeffs = 1 /\
        !x : int.
          (10 : int) ** 6 int_divides eval_int_poly coeffs x
    in
      (?coeffs : int list.
         admissible coeffs /\
         LENGTH coeffs = 26) /\
      (!coeffs : int list.
         admissible coeffs ==>
         26 <= LENGTH coeffs)``;
