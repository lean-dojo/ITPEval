(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.injective_transpose (catalog title
  "permutation.injective_transpose"): every transposition of two natural
  numbers defines an injective function on the natural numbers.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val permutation_injective_transpose =
  ``!(i : num) (j : num) (x : num) (y : num).
      (if x = i then j else if x = j then i else x) =
      (if y = i then j else if y = j then i else y) ==>
      x = y``;
