(*
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.axiom_mod_aux_body_S (catalog title
  "div_mod.axiom_mod_aux_body_S"): for every natural-number index, the source
  equality predicate relates the successor-indexed auxiliary modulus body to
  the curried binary function returning m when m is at most n and otherwise
  the recursive auxiliary value at m minus the successor of n. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_div_mod_auxiliary_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_div_mod_mod_aux",
  logipedia_div_mod_auxiliary_type);

val _ = new_constant (
  "logipedia_div_mod_mod_aux_body",
  logipedia_div_mod_auxiliary_type);

val div_mod_axiom_mod_aux_body_S =
  ``!p : num.
      logipedia_connectives_equal
        (logipedia_div_mod_mod_aux_body (SUC p))
        (\(m : num) (n : num).
            if m <= n then
              m
            else
              logipedia_div_mod_mod_aux
                p (m - SUC n) n)``;
