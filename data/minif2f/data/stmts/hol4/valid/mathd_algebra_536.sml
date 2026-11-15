(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_536: evaluation over the
  reals of 3! * (2^3 + sqrt 9) / 2 as 33. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val mathd_algebra_536 =
  ``(&(FACT 3) : real) * ((2 : real) pow 3 + sqrt 9) / 2 = 33``;
