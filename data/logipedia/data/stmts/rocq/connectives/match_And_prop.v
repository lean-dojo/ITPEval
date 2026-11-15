(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.match_And_prop (catalog title "connectives.match_And_prop"):
  the elimination principle for the module's abstract conjunction connective.
  This file contains no proof.
*)

Parameter connectives_And : Prop -> Prop -> Prop.

Theorem connectives_match_And_prop :
  forall (A : Prop), forall (B : Prop), forall (return_ : Prop),
    (A -> B -> return_) ->
    connectives_And A B ->
    return_.
Admitted.
