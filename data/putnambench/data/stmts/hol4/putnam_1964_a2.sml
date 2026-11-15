(*
  Statement-only formalization of PutnamBench artifact putnam_1964_a2:
  the classification of positive continuous real functions on the unit
  interval with prescribed normalization and first two moments as empty.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory integrationTheory;

val putnam_1964_a2 =
  ``let solution =
      \a : real. ({} : (real -> real) set)
    in
      !alpha : real.
        solution alpha =
        {f : real -> real |
           (!x : real.
              x IN interval [0, 1] ==> 0 < f x) /\
           f continuous_on interval [0, 1] /\
           integration$integral (interval [0, 1]) f = 1 /\
           integration$integral (interval [0, 1])
             (\x : real. x * f x) = alpha /\
           integration$integral (interval [0, 1])
             (\x : real. x pow 2 * f x) = alpha pow 2}``;
