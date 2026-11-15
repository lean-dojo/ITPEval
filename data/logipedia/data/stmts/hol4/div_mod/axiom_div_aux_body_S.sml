(*
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.axiom_div_aux_body_S (catalog title
  "div_mod.axiom_div_aux_body_S"): at every successor natural-number index,
  div_aux_body is equal as a curried function to the function returning zero
  when m is at most n and otherwise the successor of the recursive div_aux
  value at m minus the successor of n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_div_mod_auxiliary_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val _ = new_constant (
  "logipedia_div_mod_div_aux",
  logipedia_div_mod_auxiliary_type);

val _ = new_constant (
  "logipedia_div_mod_div_aux_body",
  logipedia_div_mod_auxiliary_type);

val div_mod_axiom_div_aux_body_S =
  ``!p : num.
      logipedia_div_mod_div_aux_body (SUC p) =
        (\(m : num) (n : num).
            if m <= n then
              0
            else
              SUC
                (logipedia_div_mod_div_aux
                   p (m - SUC n) n))``;
