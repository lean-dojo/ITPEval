(*
  Statement-only formalization of miniF2F test problem mathd_algebra_196: the identity-function
  sum of the finite real solution set of abs (2 - x) = 3 is 4. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_sigmaTheory;

val mathd_algebra_196 =
  ``!S : real set.
      FINITE S /\
      (!x : real. x IN S <=> abs (2 - x) = 3)
      ==>
      SIGMA (\x. x) S = 4``;
