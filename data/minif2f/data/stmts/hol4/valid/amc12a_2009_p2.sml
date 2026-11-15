(*
  Statement-only formalization of miniF2F valid problem amc12a_2009_p2: evaluation of a finite
  continued fraction over the rational numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory ratTheory;

val amc12a_2009_p2 =
  ``1q + 1q / (1q + 1q / (1q + 1q)) = 5q / 3q``;
