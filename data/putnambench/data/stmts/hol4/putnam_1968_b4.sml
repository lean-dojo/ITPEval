(*
  Statement-only formalization of PutnamBench artifact putnam_1968_b4:
  equality of a continuous function's symmetric improper integral with the
  corresponding integral after the substitution x - 1/x. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory integrationTheory;

val putnam_1968_b4 =
  ``!f : real -> real.
      f continuous_on UNIV /\
      (?r : real.
         ((\y : real.
             integration$integral (interval [-y, y]) f) --> r)
           at_posinfinity)
      ==>
      ?r : real.
        ((\y : real.
            integration$integral
              (interval [-y, y] DIFF interval [-1 / y, 1 / y])
              (\x : real. f (x - 1 / x))) --> r)
          at_posinfinity /\
        ((\y : real.
            integration$integral (interval [-y, y]) f) --> r)
          at_posinfinity``;
