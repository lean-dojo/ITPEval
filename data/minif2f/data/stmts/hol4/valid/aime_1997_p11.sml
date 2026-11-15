(*
  Statement-only formalization of miniF2F valid problem aime_1997_p11: the floor of one
  hundred times a ratio of finite cosine and sine sums over degree angles. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory intrealTheory
     real_sigmaTheory transcTheory;

val aime_1997_p11 =
  ``!x : real.
      x =
        sum {1 .. 44} (\n. cos (&n * pi / 180)) /
        sum {1 .. 44} (\n. sin (&n * pi / 180))
      ==>
      INT_FLOOR (100 * x) = 241``;
