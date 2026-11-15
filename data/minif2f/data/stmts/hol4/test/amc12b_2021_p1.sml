(*
  Statement-only formalization of miniF2F artifact amc12b_2021_p1: the set of integers whose
  absolute value is less than 3 times pi has cardinality 19. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pred_setTheory realTheory intrealTheory transcTheory;

val amc12b_2021_p1 =
  ``CARD {x : int | abs (real_of_int x) < 3 * pi} = 19``;
