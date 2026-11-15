(*
  Statement-only formalization of "Taylor's Theorem" from Hundred Theorems item 035.
  A sufficiently differentiable real function equals its finite Taylor sum at a base point
  plus a Lagrange remainder evaluated at an intermediate point. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory limTheory transcTheory;

val taylors_theorem =
  ``!f diff a x n.
      0 < n /\
      a <> x /\
      diff 0 = f /\
      (!m t.
         m < n /\
         min a x <= t /\ t <= max a x
         ==>
         (diff m diffl (diff (SUC m) t)) t)
      ==>
      ?t.
        min a x < t /\ t < max a x /\
        f x =
          SIGMA
            (\m. diff m a / &(FACT m) * (x - a) pow m)
            (count n) +
          diff n t / &(FACT n) * (x - a) pow n``;
