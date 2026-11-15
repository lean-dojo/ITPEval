(*
  Statement-only formalization of the Logipedia corpus artifact
  connectives.match_ex_prop (catalog title "connectives.match_ex_prop"): for
  every type, predicate P, and proposition return, a handler from each
  P-witness to return, together with the module's abstract existential
  proposition connectives.ex P, entails return. This file contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_constant (
  "logipedia_connectives_ex",
  (Type.alpha --> Type.bool) --> Type.bool);

val connectives_match_ex_prop =
  ``!(P : 'a -> bool) (return_ : bool).
      (!x : 'a. P x ==> return_) ==>
      logipedia_connectives_ex P ==>
      return_``;
