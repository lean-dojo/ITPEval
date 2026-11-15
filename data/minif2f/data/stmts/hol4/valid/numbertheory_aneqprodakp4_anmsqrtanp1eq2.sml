(*
  Statement-only formalization of miniF2F valid problem
  numbertheory_aneqprodakp4_anmsqrtanp1eq2: a real sequence defined by adding
  four to its finite prefix product satisfies a square-root identity at every
  positive index. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val numbertheory_aneqprodakp4_anmsqrtanp1eq2 =
  ``!a : num -> real.
      a 0 = 1 /\
      (!n : num.
        a (n + 1) = REAL_PROD_IMAGE a (count (n + 1)) + 4)
      ==>
      !n : num.
        1 <= n ==> a n - sqrt (a (n + 1)) = 2``;
