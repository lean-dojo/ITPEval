(*
  Statement-only formalization of miniF2F valid problem amc12a_2008_p4: evaluating the real
  telescoping product from k = 1 through 501 of (4k + 4) / (4k) as 502. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val amc12a_2008_p4 =
  ``REAL_PROD_IMAGE
      (\k : num. (4 * &k + 4) / (4 * &k))
      (IMAGE SUC (count 501)) =
    502``;
