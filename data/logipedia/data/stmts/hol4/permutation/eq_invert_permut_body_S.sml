(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.eq_invert_permut_body_S (catalog title
  "permutation.eq_invert_permut_body_S"): for every natural number n,
  Leibniz equality identifies invert_permut_body at the successor of n with
  the function returning that successor when m equals f at that successor,
  and otherwise returning invert_permut at n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_permutation_invert_permut_type =
  numSyntax.num -->
  (numSyntax.num --> numSyntax.num) -->
  numSyntax.num -->
  numSyntax.num;

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

val _ = new_constant (
  "logipedia_permutation_invert_permut",
  logipedia_permutation_invert_permut_type);

val _ = new_constant (
  "logipedia_permutation_invert_permut_body",
  logipedia_permutation_invert_permut_type);

val permutation_eq_invert_permut_body_S =
  ``!n : num.
      logipedia_leibniz
        (logipedia_permutation_invert_permut_body (SUC n))
        (\(f : num -> num) (m : num).
           if m = f (SUC n) then
             SUC n
           else
             logipedia_permutation_invert_permut n f m)``;
