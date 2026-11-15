(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_43:
  233 is the greatest natural exponent for which 15 raised to that exponent
  divides 942 factorial. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val mathd_numbertheory_43 =
  ``divides (15 EXP 233) (FACT 942) /\
    (!m : num. divides (15 EXP m) (FACT 942) ==> m <= 233)``;
