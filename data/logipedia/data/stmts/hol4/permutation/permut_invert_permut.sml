(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.permut_invert_permut (catalog title
  "permutation.permut_invert_permut"): the recursively computed inverse of a
  bounded natural-number permutation is itself a permutation within the same
  bound. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val logipedia_permutation_injn_def = new_definition (
  "logipedia_permutation_injn_def",
  ``logipedia_permutation_injn (f : num -> num) (n : num) <=>
      !i j : num.
        i <= n ==>
        j <= n ==>
        f i = f j ==>
        i = j``);

val logipedia_permutation_permut_def = new_definition (
  "logipedia_permutation_permut_def",
  ``logipedia_permutation_permut (f : num -> num) (n : num) <=>
      (!i : num. i <= n ==> f i <= n) /\
      logipedia_permutation_injn f n``);

val logipedia_permutation_invert_permut_def = Define `
  (logipedia_permutation_invert_permut 0
      (f : num -> num) (m : num) = 0) /\
  (logipedia_permutation_invert_permut (SUC n) f m =
    if m = f (SUC n) then
      SUC n
    else
      logipedia_permutation_invert_permut n f m)
`;

val permutation_permut_invert_permut =
  ``!(f : num -> num) (n : num).
      logipedia_permutation_permut f n ==>
      logipedia_permutation_permut
        (logipedia_permutation_invert_permut n f)
        n``;
