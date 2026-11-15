(*
  Statement-only formalization of miniF2F valid problem
  algebra_amgm_faxinrrp2msqrt2geq2mxm1div2x: a lower bound involving a positive
  real variable, its reciprocal, and the square root of 2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val algebra_amgm_faxinrrp2msqrt2geq2mxm1div2x =
  ``!x : real.
      0 < x
      ==>
      2 - sqrt 2 >= 2 - x - 1 / (2 * x)``;
