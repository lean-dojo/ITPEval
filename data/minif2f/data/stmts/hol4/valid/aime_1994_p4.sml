(*
  Statement-only formalization of miniF2F valid problem aime_1994_p4: a finite sum of
  floored base-2 logarithms determines a natural-number endpoint. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory transcTheory;

val aime_1994_p4 =
  ``!n : num.
      0 < n /\
      SIGMA
        (\k : num. flr (ln (&k) / ln 2))
        (IMAGE SUC (count n)) = 1994
      ==>
      n = 312``;
