(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.axiom_mod_aux_body_O (catalog title
  "div_mod.axiom_mod_aux_body_O"): the source polymorphic equality relates
  the zero-indexed modulo auxiliary body to the binary natural-number
  function that returns its first argument. This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter mod_aux_body : nat -> nat -> nat -> nat.

Theorem div_mod_axiom_mod_aux_body_O :
  connectives_equal
    (nat -> nat -> nat)
    (mod_aux_body O)
    (fun (m _n : nat) => m).
Admitted.
