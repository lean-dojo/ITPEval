(*
  Statement-only formalization of PutnamBench artifact putnam_1967_a4:
  nonexistence, for lambda greater than one half, of a real function satisfying
  a nonlinear integral equation on the closed unit interval. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory extrealTheory measureTheory;
open lebesgueTheory lebesgue_measureTheory;

val putnam_1967_a4 =
  ``!lambda : real.
      1 / 2 < lambda
      ==>
      ~(?u : real -> real.
          !x : real.
            x IN interval [0, 1]
            ==>
            u x =
              1 + lambda *
                (let restricted =
                   \y : real.
                     Normal (u y * u (y - x)) *
                     indicator_fn (interval [x, 1]) y
                 in
                   if lebesgue$integrable lebesgue restricted then
                     real (lebesgue$integral lebesgue restricted)
                   else
                     0))``;
