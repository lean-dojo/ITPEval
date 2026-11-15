(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2021_a4:
  the disk integral of the specified rational function tends to
  (sqrt 2 / 2) * pi * ln 2 as the radius tends to positive infinity.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory transcTheory
     integrationTheory;

val putnam_2021_a4 =
  ``let I =
      \R : real.
        integration$integral (interval [-R, R])
          (\x : real.
             integration$integral
               (interval
                  [-sqrt (R pow 2 - x pow 2),
                   sqrt (R pow 2 - x pow 2)])
               (\y : real.
                  (1 + 2 * x pow 2) /
                    (1 + x pow 4 + 6 * x pow 2 * y pow 2 + y pow 4) -
                  (1 + y pow 2) / (2 + x pow 4 + y pow 4)))
    in
      (I --> ((sqrt 2 / 2) * pi * ln 2)) at_posinfinity``;
