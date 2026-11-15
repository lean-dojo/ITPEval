(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.match_Or_prop (catalog title "connectives.match_Or_prop"):
  the elimination principle for the module's abstract disjunction connective.
  This file contains no proof.
*)

Parameter connectives_Or : Prop -> Prop -> Prop.

Theorem connectives_match_Or_prop :
  forall (A : Prop), forall (B : Prop), forall (return_ : Prop),
    (A -> return_) ->
    (B -> return_) ->
    connectives_Or A B ->
    return_.
Admitted.
