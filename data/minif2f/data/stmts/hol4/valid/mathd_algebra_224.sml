(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_224: the natural numbers
  whose real square roots lie strictly between 2 and 7/2 form a set of cardinality 8. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory;

val mathd_algebra_224 =
  ``FINITE
      {n : num |
         sqrt (&n : real) < 7 / 2 /\
         2 < sqrt (&n : real)}
    ==>
    CARD
      {n : num |
         sqrt (&n : real) < 7 / 2 /\
         2 < sqrt (&n : real)} =
      8``;
