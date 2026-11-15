(*
  Statement-only formalization of Logipedia corpus artifact div_mod.div_mod
  (catalog title "div_mod.div_mod"): the source's total natural-number
  quotient and remainder decompose every dividend as quotient times divisor
  plus remainder, including at divisor zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory;

val logipedia_div_mod_aux_step_def = new_definition (
  "logipedia_div_mod_aux_step_def",
  ``logipedia_div_mod_aux_step (m : num) qr =
      if SND qr <= m then
        qr
      else
        (SUC (FST qr), SND qr - SUC m)``);

val logipedia_div_mod_aux_state_def = new_definition (
  "logipedia_div_mod_aux_state_def",
  ``logipedia_div_mod_aux_state (p : num) (n : num) (m : num) =
      FUNPOW (logipedia_div_mod_aux_step m) p (0, n)``);

val logipedia_div_mod_div_aux_def = new_definition (
  "logipedia_div_mod_div_aux_def",
  ``logipedia_div_mod_div_aux (p : num) (n : num) (m : num) =
      FST (logipedia_div_mod_aux_state p n m)``);

val logipedia_div_mod_mod_aux_def = new_definition (
  "logipedia_div_mod_mod_aux_def",
  ``logipedia_div_mod_mod_aux (p : num) (n : num) (m : num) =
      SND (logipedia_div_mod_aux_state p n m)``);

val logipedia_div_mod_div_def = new_definition (
  "logipedia_div_mod_div_def",
  ``logipedia_div_mod_div (n : num) (m : num) =
      if m = 0 then
        SUC n
      else
        logipedia_div_mod_div_aux n n (PRE m)``);

val logipedia_div_mod_mod_def = new_definition (
  "logipedia_div_mod_mod_def",
  ``logipedia_div_mod_mod (n : num) (m : num) =
      if m = 0 then
        n
      else
        logipedia_div_mod_mod_aux n n (PRE m)``);

val div_mod_div_mod =
  ``!n m : num.
      n =
        logipedia_div_mod_div n m * m +
        logipedia_div_mod_mod n m``;
