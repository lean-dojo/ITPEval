(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.sym_eq_invert_permut_body_O (catalog title
  "permutation.sym_eq_invert_permut_body_O"): Leibniz equality identifies
  the function that tests whether a natural number equals f 0 and returns
  zero in either Boolean branch with invert_permut_body at zero. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_permutation_invert_permut_body_type =
  numSyntax.num -->
  (numSyntax.num --> numSyntax.num) -->
  numSyntax.num -->
  numSyntax.num;

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

val _ = new_constant (
  "logipedia_permutation_invert_permut_body",
  logipedia_permutation_invert_permut_body_type);

val permutation_sym_eq_invert_permut_body_O =
  ``logipedia_leibniz
      (\(f : num -> num) (m : num).
         if m = f 0 then 0 else 0)
      (logipedia_permutation_invert_permut_body 0)``;
