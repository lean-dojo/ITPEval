(*
  Statement-only formalization of PutnamBench artifact putnam_2008_a4:
  divergence of the reciprocal series for the real function defined by an
  exponential-threshold logarithmic recurrence. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory transcTheory;

val putnam_2008_a4 =
  ``!f : real -> real.
      (!x : real.
         f x =
         if x <= exp 1 then x else x * f (ln x))
      ==>
      ((?r : real.
          ((\N : num.
              SIGMA
                (\n : num. (1 : real) / f (&n))
                (IMAGE SUC (count N))) --> r)
            sequentially)
       <=> F)``;
