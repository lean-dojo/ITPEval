(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/gcd_EuclideanAlgorithmIterative_euclidqtvc: the iterative Euclidean
  algorithm verification condition preserving nonnegativity and the integer
  greatest common divisor across a truncated-remainder step. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory gcdTheory;

val gcd_EuclideanAlgorithmIterative_euclid_vc =
  ``let int_gcd =
      \a : int. \b : int. &(gcd (Num (ABS a)) (Num (ABS b)))
    in
      !u0 v0 : int.
        (0 : int) <= u0 ==>
        (0 : int) <= v0 ==>
        (0 : int) <= u0 /\
        (0 : int) <= v0 /\
        (!v u : int.
           (((0 : int) <= u /\ (0 : int) <= v) /\
            int_gcd u v = int_gcd u0 v0) ==>
           (if ~(v = (0 : int)) then
              ~(v = (0 : int)) /\
              ((0 : int) <= v /\ u rem v < v) /\
              ((0 : int) <= v /\ (0 : int) <= u rem v) /\
              int_gcd v (u rem v) = int_gcd u0 v0
            else
              u = int_gcd u0 v0))``;
