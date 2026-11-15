(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_b5:
  the unique positive Fibonacci indices whose difference equals the value at
  2019 of the degree-1008 polynomial interpolating the specified odd-indexed
  Fibonacci values. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory realTheory intrealTheory polyTheory;

val putnam_2019_b5 =
  ``!F : num -> int. !P : real list.
      ((!x : num.
          1 <= x
          ==>
          F (x + 2) = F (x + 1) + F x) /\
       F 1 = 1 /\
       F 2 = 1 /\
       degree P = 1008 /\
       (!n : num.
          n <= 1008
          ==>
          poly P (&(2 * n + 1) : real) =
            real_of_int (F (2 * n + 1))))
      ==>
      !j k : num.
        ((poly P 2019 = real_of_int (F j - F k) /\
          1 <= j /\
          1 <= k)
         <=>
         (j, k) = (2019, 1010))``;
