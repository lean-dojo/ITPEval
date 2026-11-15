(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1991_a3:
  the classification of real polynomials whose ordered roots have derivative
  zeros at each consecutive midpoint. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory polyTheory;

val putnam_1991_a3 =
  ``let putnam_1991_a3_solution =
      \p : real list.
        degree p = 2 /\
        ?r1 r2 : real.
          r1 <> r2 /\
          poly p r1 = 0 /\
          poly p r2 = 0
    in
      !p : real list. !n : num.
        n = degree p /\
        2 <= n
        ==>
        ((?r : num -> real.
            (!i : num.
               i < n - 1
               ==>
               r i < r (i + 1)) /\
            (!i : num.
               i < n
               ==>
               poly p (r i) = 0) /\
            (!i : num.
               i < n - 1
               ==>
               poly (diff p) ((r i + r (i + 1)) / 2) = 0))
         <=>
         putnam_1991_a3_solution p)``;
