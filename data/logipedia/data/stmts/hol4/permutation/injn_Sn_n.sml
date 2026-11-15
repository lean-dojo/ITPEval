(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.injn_Sn_n (catalog title "permutation.injn_Sn_n"): injectivity
  of a natural-number function on the interval from zero through the successor
  of n implies injectivity on the interval from zero through n. This file
  contains no proof.
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

val permutation_injn_Sn_n =
  ``!(f : num -> num) (n : num).
      logipedia_permutation_injn f (SUC n) ==>
      logipedia_permutation_injn f n``;
