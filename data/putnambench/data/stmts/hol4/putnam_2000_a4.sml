(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2000_a4:
  convergence of the improper integral from zero to positive infinity of
  sin(x) times sin(x squared). This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory transcTheory
     integrationTheory;

val putnam_2000_a4 =
  ``?y : real.
      ((\B : real.
          integration$integral (interval [0, B])
            (\x : real. sin x * sin (x pow 2))) --> y)
        at_posinfinity``;
