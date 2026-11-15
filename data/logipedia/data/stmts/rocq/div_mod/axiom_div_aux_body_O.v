(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.axiom_div_aux_body_O (catalog title
  "div_mod.axiom_div_aux_body_O"): the source polymorphic equality relates
  the zero-indexed division auxiliary body to the constant-zero binary
  natural-number function. This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter div_aux_body : nat -> nat -> nat -> nat.

Theorem div_mod_axiom_div_aux_body_O :
  connectives_equal
    (nat -> nat -> nat)
    (div_aux_body O)
    (fun (_m _n : nat) => O).
Admitted.
