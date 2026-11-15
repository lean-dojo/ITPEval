(*
  Statement-only formalization of the Logipedia corpus artifact
  leibniz.sym_leibniz (catalog title "leibniz.sym_leibniz"): Leibniz equality
  is symmetric for every type and pair of elements. This file contains no
  proof.
*)

open HolKernel Parse boolLib;

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

val leibniz_sym_leibniz =
  ``!(x : 'a) (y : 'a).
      logipedia_leibniz x y ==>
      logipedia_leibniz y x``;
