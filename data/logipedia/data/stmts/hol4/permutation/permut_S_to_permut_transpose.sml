(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.permut_S_to_permut_transpose (catalog title
  "permutation.permut_S_to_permut_transpose"): a permutation of the inclusive
  natural interval through SUC m induces a permutation through m after
  transposing its value at SUC m with SUC m. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_permutation_injn_def = new_definition (
  "logipedia_permutation_injn_def",
  ``logipedia_permutation_injn (f : num -> num) (n : num) <=>
      !(i : num) (j : num).
        i <= n ==>
        j <= n ==>
        f i = f j ==>
        i = j``);

val logipedia_permutation_permut_def = new_definition (
  "logipedia_permutation_permut_def",
  ``logipedia_permutation_permut (f : num -> num) (m : num) <=>
      (!i : num. i <= m ==> f i <= m) /\
      logipedia_permutation_injn f m``);

val logipedia_permutation_transpose_def = new_definition (
  "logipedia_permutation_transpose_def",
  ``logipedia_permutation_transpose (i : num) (j : num) (n : num) =
      if n = i then j else if n = j then i else n``);

val permutation_permut_S_to_permut_transpose =
  ``!(f : num -> num) (m : num).
      logipedia_permutation_permut f (SUC m) ==>
      logipedia_permutation_permut
        (\n. logipedia_permutation_transpose
          (f (SUC m)) (SUC m) (f n))
        m``;
