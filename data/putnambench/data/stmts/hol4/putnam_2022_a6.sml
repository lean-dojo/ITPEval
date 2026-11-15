(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_a6:
  for positive n, the largest m admitting 2n ordered real endpoints in
  (-1,1) whose odd-power interval lengths sum to 1 for k from 1 through m
  is n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_2022_a6 =
  ``!n : num.
      0 < n
      ==>
      let admissible =
        \m : num.
          ?x : num -> real.
            -1 < x 1 /\
            (!i : num.
               1 <= i /\ i < 2 * n
               ==>
               x i < x (i + 1)) /\
            x (2 * n) < 1 /\
            !k : num.
              1 <= k /\ k <= m
              ==>
              SIGMA
                (\i : num.
                   x (2 * (i + 1)) pow (2 * k - 1) -
                   x (2 * (i + 1) - 1) pow (2 * k - 1))
                (count n) =
              1
      in
        admissible n /\
        !m : num. admissible m ==> m <= n``;
