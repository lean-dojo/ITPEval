(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_a5:
  existence of a uniform real constant bounding a degree-1999 real
  polynomial's value at zero by its absolute-value integral on [-1,1].
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory integrationTheory polyTheory;

val putnam_1999_a5 =
  ``?C : real.
      !P : real list.
        degree P = 1999
        ==>
        abs (poly P 0) <=
          C *
          integration$integral (interval [~1, 1])
            (\x : real. abs (poly P x))``;
