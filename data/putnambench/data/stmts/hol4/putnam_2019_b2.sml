(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_b2:
  the normalized finite trigonometric sums in the problem converge to
  8 / pi^3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory transcTheory;

val putnam_2019_b2 =
  ``((\n : num.
        SIGMA
          (\k : num.
             sin (((2 * (&k : real) - 1) * pi) /
                  (2 * (&n : real))) /
             (cos (((&k : real) - 1) * pi /
                   (2 * (&n : real))) pow 2 *
              cos ((&k : real) * pi /
                   (2 * (&n : real))) pow 2))
          {k : num | 1 <= k /\ k < n} /
        (&n : real) pow 3) -->
      (8 / pi pow 3 : real))
    sequentially``;
