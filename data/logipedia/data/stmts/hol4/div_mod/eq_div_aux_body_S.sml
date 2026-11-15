(*
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.eq_div_aux_body_S (catalog title "div_mod.eq_div_aux_body_S"):
  for every natural-number index p, Leibniz equality identifies div_aux_body
  at SUC p with the curried function returning zero when m is at most n and
  otherwise the successor of div_aux p applied to (m - SUC n) and n. This
  file contains no proof.
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
  "logipedia_div_mod_div_aux",
  logipedia_div_mod_auxiliary_type);

val _ = new_constant (
  "logipedia_div_mod_div_aux_body",
  logipedia_div_mod_auxiliary_type);

val div_mod_eq_div_aux_body_S =
  ``!p : num.
      logipedia_leibniz
        (logipedia_div_mod_div_aux_body (SUC p))
        (\(m : num) (n : num).
            if m <= n then
              0
            else
              SUC
                (logipedia_div_mod_div_aux
                   p (m - SUC n) n))``;
