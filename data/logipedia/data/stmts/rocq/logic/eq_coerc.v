(*
  Statement-only formalization of Logipedia corpus artifact logic.eq_coerc
  (catalog title "logic.eq_coerc"): equality of propositions transports truth
  from the first proposition to the second. This file contains no proof.
*)

Theorem logic_eq_coerc :
  forall A B : Prop,
    A ->
    A = B ->
    B.
Admitted.
