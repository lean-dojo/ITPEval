(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.invert_permut_f (catalog title
  "permutation.invert_permut_f"): a recursively computed bounded inverse
  sends the value of an injective natural-number function at any index through
  n back to that index. This file contains no proof.
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

val logipedia_permutation_invert_permut_def = Define `
  (logipedia_permutation_invert_permut 0
      (f : num -> num) (m : num) = 0) /\
  (logipedia_permutation_invert_permut (SUC n) f m =
    if m = f (SUC n) then
      SUC n
    else
      logipedia_permutation_invert_permut n f m)
`;

val permutation_invert_permut_f =
  ``!(f : num -> num) (n : num) (m : num).
      m <= n ==>
      logipedia_permutation_injn f n ==>
      logipedia_permutation_invert_permut n f (f m) = m``;
