(*
  Statement-only formalization of the Logipedia corpus artifact
  leibniz.refl_leibniz (catalog title "leibniz.refl_leibniz"): for every
  type and element of that type, Leibniz equality relates the element to
  itself. This file contains no proof.
*)

open HolKernel Parse boolLib;

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

val leibniz_refl_leibniz =
  ``!x : 'a.
      logipedia_leibniz x x``;
