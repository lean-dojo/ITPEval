(*
  Statement-only formalization of miniF2F valid problem
  algebra_amgm_sumasqdivbsqgeqsumbdiva: a cyclic inequality comparing squared ratios of three
  positive real numbers with the reverse cyclic ratios. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val algebra_amgm_sumasqdivbsqgeqsumbdiva =
  ``!a b c : real.
      0 < a /\ 0 < b /\ 0 < c
      ==>
      a pow 2 / b pow 2 + b pow 2 / c pow 2 + c pow 2 / a pow 2 >=
      b / a + c / b + a / c``;
