(*
  Statement-only formalization of "The Non-Denumerability of the Continuum" from Hundred
  Theorems item 022: every sequence of real numbers omits some real number, equivalently
  there is no surjection from the natural numbers onto the reals. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val non_denumerability_of_the_continuum =
  ``!f : num -> real.
      ?x : real. !n : num. ~(x = f n)``;
