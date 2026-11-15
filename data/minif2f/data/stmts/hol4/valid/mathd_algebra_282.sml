(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_282: a real function
  defined by absolute floor on rational inputs and squared ceiling on irrational inputs has a
  specified four-value sum. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory transcTheory;

val mathd_algebra_282 =
  ``!f : real -> real.
      (!x : real.
         (?p q : int.
            q <> 0 /\ x = real_of_int p / real_of_int q)
         ==>
         f x = abs (real_of_int (INT_FLOOR x))) /\
      (!x : real.
         ~(?p q : int.
             q <> 0 /\ x = real_of_int p / real_of_int q)
         ==>
         f x = (real_of_int (INT_CEILING x)) pow 2)
      ==>
      f ((8 : real) powr (1 / 3)) +
        f (~pi) +
        f (sqrt 50) +
        f (9 / 2) =
        79``;
