(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1983_a5:
  existence of a positive real number whose nth-power floor differs from n by
  an even integer for every positive natural n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory realTheory intrealTheory;

val putnam_1983_a5 =
  ``let putnam_1983_a5_solution = T
    in
      ((?alpha : real.
          0 < alpha /\
          !n : num.
            0 < n
            ==>
            (2 : int) int_divides
              (INT_FLOOR (alpha pow n) - int_of_num n))
       <=>
       putnam_1983_a5_solution)``;
