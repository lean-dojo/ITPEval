(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q810431, "Basel problem": the real series of reciprocal squares over the
  natural numbers sums to pi squared divided by six. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory seqTheory transcTheory;

val hasSum_zeta_two =
  ``(\n : num. (1 : real) / (&n : real) pow 2)
    sums (pi pow 2 / 6)``;
