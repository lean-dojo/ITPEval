(*
  Statement-only formalization of miniF2F valid artifact imo_1962_p4: classification of the
  real solutions of a three-term squared-cosine equation into integer-indexed families. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory transcTheory;

val _ = new_theory "hello";

val imo_1962_p4 =
  ``!x : real.
      (cos x) pow 2 + (cos (2 * x)) pow 2 + (cos (3 * x)) pow 2 = 1
      ==>
      (?m : int. x = pi / 2 + real_of_int m * pi) \/
      (?m : int. x = pi / 4 + real_of_int m * pi / 2) \/
      (?m : int. x = pi / 6 + real_of_int m * pi / 3)``;

val _ = export_theory();
