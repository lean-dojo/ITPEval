(*
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.le_mod_aux_m_m (catalog title "div_mod.le_mod_aux_m_m"): for all
  natural-number fuel bounds p, dividends n, and modulus predecessors m, if
  n is at most p then the fuel-recursive auxiliary remainder is at most m.
  This file contains no proof.
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

val logipedia_div_mod_mod_aux_def = new_definition (
  "logipedia_div_mod_mod_aux_def",
  ``logipedia_div_mod_mod_aux (p : num) (n : num) (m : num) =
      SND (logipedia_div_mod_aux_state p n m)``);

val div_mod_le_mod_aux_m_m =
  ``!p n m : num.
      n <= p
      ==>
      logipedia_div_mod_mod_aux p n m <= m``;
