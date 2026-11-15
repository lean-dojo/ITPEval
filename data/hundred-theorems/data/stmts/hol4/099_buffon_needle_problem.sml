(*
  Statement-only formalization of "Buffon Needle Problem" from Hundred Theorems
  artifact hundred-theorems__hol4__099. For a needle of positive length dropped
  with independent uniform distance and angle, it states the short- and
  long-needle crossing probabilities. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory;
open extrealTheory measureTheory borelTheory probabilityTheory;

val buffon_needle_problem =
  ``let uniform_on =
      \(p : 'a p_space) (Z : 'a -> real) (a : real) (b : real).
        random_variable Z p borel /\
        a < b /\
        !t.
          distribution_function p Z t =
          if t < a then 0
          else if b <= t then 1
          else Normal ((t - a) / (b - a))
    in
      !(p : 'a p_space) (X : 'a -> real) (Theta : 'a -> real)
       (l : real) (d : real).
        prob_space p /\
        0 < l /\
        0 < d /\
        uniform_on p X 0 (d / 2) /\
        uniform_on p Theta 0 pi /\
        indep_rv p X Theta borel borel
        ==>
        prob p
          {w |
             w IN p_space p /\
             X w <= (l / 2) * sin (Theta w)} =
        Normal
          (if l <= d then
             (2 * l) / (pi * d)
           else
             (2 / (pi * d)) *
             (l - sqrt (l pow 2 - d pow 2) + d * acs (d / l)))``;
