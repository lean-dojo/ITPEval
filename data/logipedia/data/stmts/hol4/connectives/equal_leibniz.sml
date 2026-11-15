(*
  Statement-only formalization of the Logipedia corpus artifact
  connectives.equal_leibniz (catalog title "connectives.equal_leibniz"): for
  every type, elements x and y, and predicate P, the module's abstract
  equality of x and y transports P x to P y. This file contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val connectives_equal_leibniz =
  ``!(x : 'a) (y : 'a).
      logipedia_connectives_equal x y ==>
      !P : 'a -> bool.
        P x ==> P y``;
