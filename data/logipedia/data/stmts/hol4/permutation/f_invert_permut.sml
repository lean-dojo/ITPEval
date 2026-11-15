(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.f_invert_permut (catalog title
  "permutation.f_invert_permut"): applying a bounded permutation to its
  recursively defined inverse lookup recovers every natural number in the
  bounded interval. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val logipedia_permutation_permut_def = new_definition (
  "logipedia_permutation_permut_def",
  ``logipedia_permutation_permut (f : num -> num) (n : num) <=>
      (!i : num. i <= n ==> f i <= n) /\
      !i j : num.
        i <= n ==>
        j <= n ==>
        f i = f j ==>
        i = j``);

val logipedia_permutation_invert_permut_def = Define `
  (logipedia_permutation_invert_permut 0
      (f : num -> num) (m : num) = 0) /\
  (logipedia_permutation_invert_permut (SUC n) f m =
    if m = f (SUC n) then
      SUC n
    else
      logipedia_permutation_invert_permut n f m)
`;

val permutation_f_invert_permut =
  ``!(f : num -> num) (n : num) (m : num).
      m <= n ==>
      logipedia_permutation_permut f n ==>
      f (logipedia_permutation_invert_permut n f m) = m``;
