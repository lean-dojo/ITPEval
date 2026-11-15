(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_81:
  the natural-number remainder computation 71 MOD 3 = 2. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_81 =
  ``((71 : num) MOD 3 = 2)``;
