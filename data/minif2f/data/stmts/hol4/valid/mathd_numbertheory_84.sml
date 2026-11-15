(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_84:
  the integer floor of the real calculation (9 / 160) * 100 is 5. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory;

val mathd_numbertheory_84 =
  ``INT_FLOOR ((9 : real) / 160 * 100) = (5 : int)``;
