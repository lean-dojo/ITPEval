(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_185: the cardinality of
  the integer solution set of an absolute-value inequality. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pred_setTheory;

val mathd_algebra_185 =
  ``!f : int -> int.
      (!x : int. f x = ABS (x + 4)) /\
      FINITE {x : int | f x < 9}
      ==>
      CARD {x : int | f x < 9} = 17``;
