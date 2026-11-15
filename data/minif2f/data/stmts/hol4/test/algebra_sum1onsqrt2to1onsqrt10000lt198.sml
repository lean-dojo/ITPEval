(*
  Statement-only formalization of miniF2F test problem
  algebra_sum1onsqrt2to1onsqrt10000lt198: the sum of the reciprocal square
  roots of the natural numbers from 2 through 10000 is less than 198. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val algebra_sum1onsqrt2to1onsqrt10000lt198 =
  ``sum {2 .. 10000} (\k. 1 / sqrt (&k)) < 198``;
