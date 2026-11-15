(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_303:
  the finite set of natural moduli at least 2 satisfying two specified
  congruences has element sum 111. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val mathd_numbertheory_303 =
  ``!S : num set.
      FINITE S /\
      (!n : num.
         n IN S <=>
         2 <= n /\
         171 MOD n = 80 MOD n /\
         468 MOD n = 13 MOD n)
      ==>
      SIGMA (\k : num. k) S = 111``;
