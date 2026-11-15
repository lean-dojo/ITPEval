(*
  Statement-only formalization of PutnamBench artifact putnam_1977_b1:
  the finite products from n = 2 through N of (n^3 - 1) / (n^3 + 1)
  converge to 2/3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory;

val putnam_1977_b1 =
  ``((\N : num.
       REAL_PROD_IMAGE
         (\n : num.
            (((&n : real) pow 3 - 1) /
             ((&n : real) pow 3 + 1)))
         (count (SUC N) DIFF count 2)) -->
     (2 / 3 : real))
    sequentially``;
