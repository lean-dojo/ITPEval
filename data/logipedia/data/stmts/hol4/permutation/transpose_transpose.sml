(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.transpose_transpose (catalog title
  "permutation.transpose_transpose"): transposing two natural numbers is an
  involution on the natural numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_permutation_transpose_def = new_definition (
  "logipedia_permutation_transpose_def",
  ``logipedia_permutation_transpose (i : num) (j : num) (n : num) =
      if n = i then j else if n = j then i else n``);

val permutation_transpose_transpose =
  ``!(i : num) (j : num) (n : num).
      logipedia_permutation_transpose i j
        (logipedia_permutation_transpose i j n) = n``;
