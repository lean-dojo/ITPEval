(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1998_a4:
  the decimal numbers formed by Fibonacci-style concatenation are divisible
  by 11 exactly at positive indices congruent to 1 modulo 6. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory listTheory pred_setTheory;

val putnam_1998_a4 =
  ``let from_digits =
      \digits : num list.
        FOLDL
          (\acc : num. \digit : num. 10 * acc + digit)
          0
          digits
    in
      !A : num -> num list.
        A 1 = [0] /\
        A 2 = [1] /\
        (!n : num.
           0 < n
           ==>
           A (n + 2) = A (n + 1) ++ A n)
        ==>
        {n : num |
           1 <= n /\ divides 11 (from_digits (A n))} =
        {n : num | n MOD 6 = 1}``;
