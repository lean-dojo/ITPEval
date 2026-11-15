(*
  Statement-only formalization of the Logipedia corpus artifact
  connectives.falsity (catalog title "connectives.falsity"): the module's
  abstract falsity proposition entails every proposition. This file contains
  no proof.
*)

open HolKernel Parse boolLib;

val _ = new_constant (
  "logipedia_connectives_False",
  Type.bool);

val connectives_falsity =
  ``!t : bool.
      logipedia_connectives_False ==> t``;
