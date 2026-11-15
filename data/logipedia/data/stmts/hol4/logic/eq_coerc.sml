(*
  Statement-only formalization of the Logipedia corpus artifact logic.eq_coerc
  (catalog title "logic.eq_coerc"): equality of propositions transports truth
  from the first proposition to the second. This file contains no proof.
*)

open HolKernel Parse boolLib;

val logic_eq_coerc =
  ``!A B : bool.
      A ==> (A = B) ==> B``;
