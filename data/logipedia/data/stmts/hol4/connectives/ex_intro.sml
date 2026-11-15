(*
  Statement-only formalization of the Logipedia corpus artifact
  connectives.ex_intro (catalog title "connectives.ex_intro"): for every type,
  predicate P, and element x, P x entails the module's abstract existential
  proposition connectives.ex P. This file contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_constant (
  "logipedia_connectives_ex",
  (Type.alpha --> Type.bool) --> Type.bool);

val connectives_ex_intro =
  ``!(P : 'a -> bool) (x : 'a).
      P x ==> logipedia_connectives_ex P``;
