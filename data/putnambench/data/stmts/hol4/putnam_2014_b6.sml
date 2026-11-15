(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_b6:
  a Lipschitz real function on the unit interval whose values at rational
  points are integer-affine is affine on each interval of a finite interval
  cover. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pred_setTheory realTheory intrealTheory ratTheory
     real_of_ratTheory;

val putnam_2014_b6 =
  ``!f : real -> real.
      ((?K : real.
          0 < K /\
          !x y : real.
            0 <= x /\ x <= 1 /\ 0 <= y /\ y <= 1
            ==>
            abs (f x - f y) <= K * abs (x - y)) /\
       (!r : rat.
          0q <= r /\ r <= 1q
          ==>
          ?a b : int.
            f (real_of_rat r) =
              real_of_int a + real_of_int b * real_of_rat r))
      ==>
      ?I : (real set) set.
        FINITE I /\
        (!J : real set.
           J IN I
           ==>
           (?a b : real.
              a <= b /\ J = {x : real | a <= x /\ x <= b}) /\
           (?m c : real.
              !x : real.
                x IN J ==> f x = c + m * x)) /\
        {x : real | 0 <= x /\ x <= 1} = BIGUNION I``;
