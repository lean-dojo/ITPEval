(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1987_a6:
  convergence of the series x^(a(n))/n^3, where a(n) counts zeroes in the
  base-3 representation of n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory numposrepTheory pred_setTheory realTheory
     seqTheory;

val putnam_1987_a6 =
  ``let digits_b3 =
      \n : num. if n = 0 then [0] else n2l 3 n
    in
    let a =
      \n : num.
        LENGTH (FILTER (\d : num. d = 0) (digits_b3 n))
    in
      {x : real |
         0 < x /\
         summable
           (\n : num.
              x pow (a n) / ((&n : real) pow 3))} =
      {x : real | 0 < x /\ x < 25}``;
