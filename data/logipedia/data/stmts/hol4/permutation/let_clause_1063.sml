(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.let_clause_1063 (catalog title "permutation.let_clause_1063"):
  equal bounded inputs to a natural-number permutation have the same image,
  with all bounds, image equations, range, and injectivity assumptions retained.
  This file contains no proof.
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
  ``logipedia_permutation_permut (f : num -> num) (n : num) <=>
      (!i : num. i <= n ==> f i <= n) /\
      logipedia_permutation_injn f n``);

val permutation_let_clause_1063 =
  ``!(f : num -> num) (n : num).
      logipedia_permutation_permut f n ==>
      !(i : num) (j : num).
        i <= n ==>
        j <= n ==>
        !a : num.
          (a <= n /\ f a = i) ==>
          a <= n ==>
          f a = i ==>
          !b : num.
            (b <= n /\ f b = j) ==>
            b <= n ==>
            f b = j ==>
            (!i0 : num. i0 <= n ==> f i0 <= n) ==>
            logipedia_permutation_injn f n ==>
            a = b ==>
            f a = j``;
