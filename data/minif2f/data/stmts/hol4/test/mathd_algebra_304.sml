(*
  Statement-only formalization of miniF2F test problem mathd_algebra_304: the natural-number
  square identity 91 squared equals 8281. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_algebra_304 = ``(91 : num) ** 2 = 8281``;
