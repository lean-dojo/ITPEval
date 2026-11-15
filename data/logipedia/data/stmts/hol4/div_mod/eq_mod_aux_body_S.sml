(*
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.eq_mod_aux_body_S (catalog title "div_mod.eq_mod_aux_body_S"):
  for every natural-number index p, Leibniz equality identifies mod_aux_body
  at SUC p with the curried function returning m when m is at most n and
  otherwise mod_aux p applied to (m - SUC n) and n. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_div_mod_auxiliary_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

val _ = new_constant (
  "logipedia_div_mod_mod_aux",
  logipedia_div_mod_auxiliary_type);

val _ = new_constant (
  "logipedia_div_mod_mod_aux_body",
  logipedia_div_mod_auxiliary_type);

val div_mod_eq_mod_aux_body_S =
  ``!p : num.
      logipedia_leibniz
        (logipedia_div_mod_mod_aux_body (SUC p))
        (\(m : num) (n : num).
            if m <= n then
              m
            else
              logipedia_div_mod_mod_aux
                p (m - SUC n) n)``;
