(*
  Statement-only formalization of PutnamBench artifact putnam_1967_a6:
  the maximum number of sign patterns of nowhere-zero solutions to two
  homogeneous real linear equations in four variables is eight. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_1967_a6 =
  ``let sign_patterns =
      \a : num -> real.
      \b : num -> real.
        {s : num -> real |
           (!i : num. 4 <= i ==> s i = 0) /\
           ?x : num -> real.
             (!i : num. i < 4 ==> x i <> 0) /\
             SIGMA (\i : num. a i * x i) (count 4) = 0 /\
             SIGMA (\i : num. b i * x i) (count 4) = 0 /\
             (!i : num. i < 4 ==> s i = sgn (x i))}
    in
      (?a b : num -> real.
         a 0 * b 1 - a 1 * b 0 <> 0 /\
         CARD (sign_patterns a b) = 8) /\
      (!a b : num -> real.
         a 0 * b 1 - a 1 * b 0 <> 0
         ==>
         CARD (sign_patterns a b) <= 8)``;
