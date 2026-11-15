(*
  Statement-only formalization of PutnamBench artifact putnam_1970_b1:
  the scaled finite product of (n squared plus i squared) to the power 1/n
  converges to exp (2 * ln 5 - 4 + 2 * arctan 2). This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory transcTheory;

val putnam_1970_b1 =
  ``((\n : num.
       1 / ((&n : real) pow 4) *
       REAL_PROD_IMAGE
         (\i : num.
            (((&n : real) pow 2 + (&i : real) pow 2) powr
               (1 / (&n : real))))
         (IMAGE SUC (count (2 * n)))) -->
     exp (2 * ln 5 - 4 + 2 * atn 2))
    sequentially``;
