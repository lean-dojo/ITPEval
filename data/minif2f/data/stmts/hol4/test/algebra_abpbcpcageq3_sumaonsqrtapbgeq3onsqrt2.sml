(*
  Statement-only formalization of miniF2F test problem
  algebra_abpbcpcageq3_sumaonsqrtapbgeq3onsqrt2: a cyclic square-root inequality
  for positive real numbers under a lower bound on ab + bc + ca. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val algebra_abpbcpcageq3_sumaonsqrtapbgeq3onsqrt2 =
  ``!a b c : real.
      0 < a /\ 0 < b /\ 0 < c /\
      3 <= a * b + b * c + c * a
      ==>
      3 / sqrt 2 <=
        a / sqrt (a + b) +
        b / sqrt (b + c) +
        c / sqrt (c + a)``;
