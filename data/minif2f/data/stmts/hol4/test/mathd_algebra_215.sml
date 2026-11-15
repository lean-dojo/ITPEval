(*
  Statement-only formalization of miniF2F artifact mathd_algebra_215: the sum of all real
  solutions of (x + 3)^2 = 121 is -6. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_sigmaTheory;

val mathd_algebra_215 =
  ``!S : real set.
      FINITE S /\
      (!x : real. x IN S <=> (x + 3) pow 2 = 121)
      ==>
      SIGMA (\x. x) S = -6``;
