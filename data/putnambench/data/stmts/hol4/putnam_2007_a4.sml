(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_a4:
  the classification of real polynomials that map every decimal repunit to a
  decimal repunit. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory intrealTheory
     real_sigmaTheory polyTheory transcTheory;

val putnam_2007_a4 =
  ``let repunit =
      \x : real.
        ?m : num.
          x =
            &SIGMA
              (\i : num. 10 EXP i)
              (count (SUC m))
    in
      !p : real list.
        ((!x : real. repunit x ==> repunit (poly p x)) <=>
         ?d : num. ?c : int.
           c >= 1 - int_of_num d /\
           !x : real.
             poly p x =
               (((10 : real) powr real_of_int c) *
                  (9 * x + 1) pow d -
                1) /
               9)``;
