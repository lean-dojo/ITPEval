(*
  Statement-only formalization of PutnamBench artifact putnam_1968_a4:
  the sum of squared pairwise distances among finitely many points on the
  unit sphere in real three-space is at most the square of their number.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_1968_a4 =
  ``let norm_sq3 =
      \P : (real # real) # real.
        FST (FST P) pow 2 +
        SND (FST P) pow 2 +
        SND P pow 2
    in
    let dist_sq3 =
      \P Q : (real # real) # real.
        (FST (FST P) - FST (FST Q)) pow 2 +
        (SND (FST P) - SND (FST Q)) pow 2 +
        (SND P - SND Q) pow 2
    in
      !n : num. !S : num -> (real # real) # real.
        (!i : num. i < n ==> norm_sq3 (S i) = 1)
        ==>
        SIGMA
          (\i : num.
             SIGMA
               (\j : num.
                  if i < j then dist_sq3 (S i) (S j) else 0)
               (count n))
          (count n)
        <= (&n : real) pow 2``;
