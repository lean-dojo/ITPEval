(*
  Statement-only formalization of the Logipedia corpus artifact
  connectives.nmk (catalog title "connectives.nmk"): for every proposition A,
  a function from A to the module's abstract falsity proposition entails the
  module's abstract negation connectives.Not A. This file contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_constant (
  "logipedia_connectives_False",
  Type.bool);

val _ = new_constant (
  "logipedia_connectives_Not",
  Type.bool --> Type.bool);

val connectives_nmk =
  ``!A : bool.
      (A ==> logipedia_connectives_False) ==>
      logipedia_connectives_Not A``;
