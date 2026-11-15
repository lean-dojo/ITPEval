(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_b6:
  infinitely many ordered pairs of integers preserve triangular-number
  membership for every positive integer input. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory pred_setTheory;

val putnam_1988_b6 =
  ``let triangular =
      \x : int.
        ?n : int.
          0 <= n /\ 2 * x = n * (n + 1)
    in
      INFINITE
        {ab : int # int |
           !t : int.
             0 < t
             ==>
             (triangular (FST ab * t + SND ab) <=>
              triangular t)}``;
