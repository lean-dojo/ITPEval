(*
  Statement-only formalization of miniF2F valid problem amc12a_2015_p10: positive ordered
  integers satisfying x + y + x * y = 80 have x = 26. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val _ = new_theory "hello";

val amc12a_2015_p10 =
  ``!x y : int.
      0 < y /\
      y < x /\
      x + y + x * y = 80
      ==>
      x = 26``;

val _ = export_theory();
