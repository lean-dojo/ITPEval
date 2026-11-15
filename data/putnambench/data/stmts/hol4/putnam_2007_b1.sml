(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_b1:
  the divisibility criterion for a nonconstant integer polynomial with
  nonnegative coefficients evaluated at a positive integer. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory;

val putnam_2007_b1 =
  ``let eval_int_poly =
      \coeffs : int list.
      \x : int.
        FOLDR (\c acc. c + x * acc) 0 coeffs
    in
      !f : int list. !n : int.
        (!i : num. i < LENGTH f ==> 0 <= EL i f) /\
        (?i : num. 0 < i /\ i < LENGTH f /\ 0 < EL i f) /\
        0 < n
        ==>
        ((eval_int_poly f n) int_divides
           (eval_int_poly f (eval_int_poly f n + 1)) <=>
         n = 1)``;
