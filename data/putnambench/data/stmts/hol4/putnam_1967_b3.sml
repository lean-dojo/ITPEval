(*
  Statement-only formalization of PutnamBench artifact putnam_1967_b3:
  the limiting integral identity for two continuous real functions of period
  one, with one function evaluated at increasingly rapid integer dilations.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory integrationTheory;

val putnam_1967_b3 =
  ``!f g : real -> real.
      f continuous_on UNIV /\
      g continuous_on UNIV /\
      (!x : real. f (x + 1) = f x) /\
      (!x : real. g (x + 1) = g x)
      ==>
      ((\n : num.
          integration$integral (interval [0, 1])
            (\x : real. f x * g (&n * x))) -->
       (integration$integral (interval [0, 1]) f *
        integration$integral (interval [0, 1]) g))
        sequentially``;
