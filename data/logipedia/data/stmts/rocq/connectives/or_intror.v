(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.or_intror (catalog title "connectives.or_intror"): the right
  introduction principle for the module's abstract disjunction connective.
  This file contains no proof.
*)

Parameter connectives_Or : Prop -> Prop -> Prop.

Theorem connectives_or_intror :
  forall (A : Prop), forall (B : Prop),
    B ->
    connectives_Or A B.
Admitted.
