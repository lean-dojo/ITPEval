(*
  Statement-only formalization of miniF2F test problem imo_1969_p2: zeros of a
  finite cosine sum differ by an integer multiple of pi. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory intrealTheory
     real_sigmaTheory transcTheory;

val _ = new_theory "hello";

val imo_1969_p2 =
  ``!m n : real. !k : num. !a : num -> real. !y : real -> real.
      0 < k /\
      (!x : real.
         y x =
         SIGMA (\i. cos (a i + x) / ((2 : real) pow i)) (count k)) /\
      y m = 0 /\
      y n = 0
      ==>
      ?t : int. m - n = real_of_int t * pi``;

val _ = export_theory();
