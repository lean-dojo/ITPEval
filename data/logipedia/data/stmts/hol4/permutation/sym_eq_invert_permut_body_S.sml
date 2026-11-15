(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.sym_eq_invert_permut_body_S (catalog title
  "permutation.sym_eq_invert_permut_body_S"): at each successor stage,
  invert_permut_body is Leibniz-equal to the function that returns the stage
  when its input equals the function's value there, and otherwise uses the
  preceding invert_permut operation. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_permutation_operator_type =
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
  logipedia_permutation_operator_type);

val _ = new_constant (
  "logipedia_permutation_invert_permut_body",
  logipedia_permutation_operator_type);

val permutation_sym_eq_invert_permut_body_S =
  ``!n : num.
      logipedia_leibniz
        (\f : num -> num. \m : num.
           if m = f (SUC n) then
             SUC n
           else
             logipedia_permutation_invert_permut n f m)
        (logipedia_permutation_invert_permut_body (SUC n))``;
