(*
  Statement-only formalization of Logipedia corpus artifact logic.absurd
  (catalog title "logic.absurd"): a proposition together with its abstract
  negation entails the module's abstract falsity proposition. This file
  contains no proof.
*)

Parameter connectives_False : Prop.
Parameter connectives_Not : Prop -> Prop.

Theorem logic_absurd :
  forall A : Prop,
    A ->
    connectives_Not A ->
    connectives_False.
Admitted.
