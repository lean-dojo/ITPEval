(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.axiom_invert_permut_body_O (catalog title
  "permutation.axiom_invert_permut_body_O"): at natural-number index zero,
  connectives.equal relates invert_permut_body to the curried function that
  applies the Boolean matcher to two zero branches and the equality test of
  m with f zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_permutation_invert_permut_body_type =
  numSyntax.num -->
  (numSyntax.num --> numSyntax.num) -->
  numSyntax.num -->
  numSyntax.num;

val logipedia_nat_eqb_type =
  numSyntax.num -->
  numSyntax.num -->
  Type.bool;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_bool_match_bool_type",
  Type.alpha --> Type.alpha --> Type.bool --> Type.alpha);

val _ = new_constant (
  "logipedia_nat_eqb",
  logipedia_nat_eqb_type);

val _ = new_constant (
  "logipedia_permutation_invert_permut_body",
  logipedia_permutation_invert_permut_body_type);

val permutation_axiom_invert_permut_body_O =
  ``logipedia_connectives_equal
      (logipedia_permutation_invert_permut_body 0)
      (\(f : num -> num) (m : num).
         logipedia_bool_match_bool_type
           0
           0
           (logipedia_nat_eqb m (f 0)))``;
