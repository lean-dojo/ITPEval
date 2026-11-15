(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.transpose_i_j_j (catalog title
  "permutation.transpose_i_j_j"): swapping two natural numbers sends the
  second selected number to the first. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_permutation_transpose_def = new_definition (
  "logipedia_permutation_transpose_def",
  ``logipedia_permutation_transpose (i : num) (j : num) (n : num) =
      if n = i then j else if n = j then i else n``);

val permutation_transpose_i_j_j =
  ``!i j : num. logipedia_permutation_transpose i j j = i``;
