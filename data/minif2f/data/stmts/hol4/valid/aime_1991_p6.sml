(*
  Statement-only formalization of miniF2F valid problem aime_1991_p6: a finite sum of floor
  values over consecutive natural numbers determines the floor of a scaled real. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory intrealTheory;

val aime_1991_p6 =
  ``!r : real.
      ITSET
        (\k acc. INT_FLOOR (r + &k / 100) + acc)
        (IMAGE (\i : num. 19 + i) (count 73))
        (0 : int) = 546
      ==>
      INT_FLOOR (100 * r) = 743``;
