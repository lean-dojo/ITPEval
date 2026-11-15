(*
  Statement-only formalization of miniF2F test problem amc12a_2021_p9: the natural-number
  product over k = 0,...,6 of 2^(2^k) + 3^(2^k) equals 3^128 - 2^128. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val amc12a_2021_p9 =
  ``PROD_IMAGE (\k : num. 2 ** (2 ** k) + 3 ** (2 ** k)) (count 7) =
      3 ** 128 - 2 ** 128``;
