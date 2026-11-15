(*
  Statement-only formalization of miniF2F test problem amc12b_2002_p2: evaluating an integer
  polynomial expression when x equals 4. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val _ = new_theory "hello";

val amc12b_2002_p2 =
  ``!x : int.
      x = 4
      ==>
      (3 * x - 2) * (4 * x + 1) -
      (3 * x - 2) * (4 * x) + 1 = 11``;

val _ = export_theory();
