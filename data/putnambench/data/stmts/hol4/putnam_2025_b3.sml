(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_b3
  (putnambench__hol4__putnam_2025_b3): every nonempty set of positive natural
  numbers closed under taking positive divisors of 2025^n - 15^n is the set
  of all positive natural numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val putnam_2025_b3 =
  ``let putnam_2025_b3_solution = T
    in
      putnam_2025_b3_solution <=>
      !S : num set.
        S <> {} /\
        (!n : num. n IN S ==> 0 < n) /\
        (!n d : num.
           n IN S /\
           0 < d /\
           divides d (2025 EXP n - 15 EXP n)
           ==>
           d IN S)
        ==>
        S = {n : num | 0 < n}``;
