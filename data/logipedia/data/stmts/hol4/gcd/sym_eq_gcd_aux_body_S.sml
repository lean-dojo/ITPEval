(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.sym_eq_gcd_aux_body_S (catalog title "gcd.sym_eq_gcd_aux_body_S"):
  for every natural-number index, Leibniz equality identifies the curried
  function that returns n when the source divisibility test on n and m is
  true, and otherwise returns gcd_aux p n (m mod n), with gcd_aux_body at the
  successor index. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_gcd_auxiliary_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

val _ = new_constant (
  "logipedia_gcd_gcd_aux",
  logipedia_gcd_auxiliary_type);

val _ = new_constant (
  "logipedia_gcd_gcd_aux_body",
  logipedia_gcd_auxiliary_type);

val gcd_sym_eq_gcd_aux_body_S =
  ``!p : num.
      logipedia_leibniz
        (\(m : num) (n : num).
           if m MOD n = 0 then
             n
           else
             logipedia_gcd_gcd_aux p n (m MOD n))
        (logipedia_gcd_gcd_aux_body (SUC p))``;
