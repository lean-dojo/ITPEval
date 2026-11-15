(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_85:
  evaluating the natural-number base-three expansion 1*3^3 + 2*3^2 + 2*3 + 2
  as 53. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_85 =
  ``1 * 3 EXP 3 + 2 * 3 EXP 2 + 2 * 3 + 2 = (53 : num)``;
