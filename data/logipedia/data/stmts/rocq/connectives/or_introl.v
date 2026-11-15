(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.or_introl (catalog title "connectives.or_introl"): the left
  introduction principle for the module's abstract disjunction connective.
  This file contains no proof.
*)

Parameter connectives_Or : Prop -> Prop -> Prop.

Theorem connectives_or_introl :
  forall (A : Prop), forall (B : Prop),
    A ->
    connectives_Or A B.
Admitted.
