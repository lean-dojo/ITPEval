(*
  Statement-only formalization of PutnamBench artifact putnam_1974_b5:
  every natural-number partial sum of the exponential series through its
  own index is strictly greater than half the corresponding exponential.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory transcTheory;

val putnam_1974_b5 =
  ``!n : num.
      SIGMA
        (\i : num. (&n : real) pow i / &(FACT i))
        (count (n + 1)) >
      exp (&n) / 2``;
