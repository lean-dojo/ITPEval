(*
  Statement-only formalization of miniF2F test artifact mathd_algebra_170:
  the cardinality of the integers whose real distance from 2 is at most 5.6.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pred_setTheory realTheory intrealTheory;

val _ = new_theory "hello";

val mathd_algebra_170 =
  ``!S : int set.
      FINITE S /\
      (!n : int.
         n IN S <=>
         abs (real_of_int n - 2) <= 5 + 6 / 10)
      ==>
      CARD S = 11``;

val _ = export_theory();
