(*
  Statement-only formalization of miniF2F test problem
  algebra_absapbon1pabsapbleqsumabsaon1pabsa: a normalized absolute-value
  inequality for the sum of two real numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val algebra_absapbon1pabsapbleqsumabsaon1pabsa =
  ``!a b : real.
      abs (a + b) / (1 + abs (a + b)) <=
        abs a / (1 + abs a) + abs b / (1 + abs b)``;
