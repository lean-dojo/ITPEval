(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.axiom_mod_aux_body_S (catalog title
  "div_mod.axiom_mod_aux_body_S"): the source polymorphic equality relates
  each successor-indexed modulo auxiliary body to the binary natural-number
  function that returns its first input when it is at most its second, and
  otherwise returns mod_aux at the predecessor index after truncated
  subtraction by the second input's successor. This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter mod_aux mod_aux_body : nat -> nat -> nat -> nat.

Theorem div_mod_axiom_mod_aux_body_S :
  forall p : nat,
    connectives_equal
      (nat -> nat -> nat)
      (mod_aux_body (S p))
      (fun m n : nat =>
         if Nat.leb m n
         then m
         else mod_aux p (m - S n) n).
Admitted.
