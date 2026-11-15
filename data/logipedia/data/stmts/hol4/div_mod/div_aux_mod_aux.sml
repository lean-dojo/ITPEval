(*
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.div_aux_mod_aux (catalog title "div_mod.div_aux_mod_aux"): the
  fuel-recursive auxiliary quotient and remainder decompose every natural
  number into a multiple of the successor divisor plus the remainder.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory;

val logipedia_div_mod_aux_step_def = new_definition (
  "logipedia_div_mod_aux_step_def",
  ``logipedia_div_mod_aux_step (m : num) qr =
      COND (SND qr <= m)
        qr
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

val div_mod_div_aux_mod_aux =
  ``!p n m : num.
      n =
        logipedia_div_mod_div_aux p n m * SUC m +
        logipedia_div_mod_mod_aux p n m``;
