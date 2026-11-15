(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q22952648, "Uncountability of the continuum": the universal set of real
  numbers is not countable. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory;

val not_countable_real =
  ``~COUNTABLE (UNIV : real set)``;
