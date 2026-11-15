(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.axiom_invert_permut_body_S (catalog title
  "permutation.axiom_invert_permut_body_S"): for every natural number n,
  connectives.equal relates invert_permut_body at the successor of n to the
  curried function selecting that successor or invert_permut at n via the
  source Boolean matcher and equality test. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_permutation_invert_permut_type =
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
  "logipedia_permutation_invert_permut",
  logipedia_permutation_invert_permut_type);

val _ = new_constant (
  "logipedia_permutation_invert_permut_body",
  logipedia_permutation_invert_permut_type);

val permutation_axiom_invert_permut_body_S =
  ``!n : num.
      logipedia_connectives_equal
        (logipedia_permutation_invert_permut_body (SUC n))
        (\(f : num -> num) (m : num).
           logipedia_bool_match_bool_type
             (SUC n)
             (logipedia_permutation_invert_permut n f m)
             (logipedia_nat_eqb m (f (SUC n))))``;
