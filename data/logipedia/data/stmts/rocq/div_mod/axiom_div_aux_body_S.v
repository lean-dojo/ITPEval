(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.axiom_div_aux_body_S (catalog title
  "div_mod.axiom_div_aux_body_S"): the source polymorphic equality relates
  each successor-indexed division auxiliary body to the binary natural-number
  function that returns zero when its first input is at most its second, and
  otherwise returns the successor of div_aux at the predecessor index after
  truncated subtraction by the second input's successor. This file contains
  no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter div_aux div_aux_body : nat -> nat -> nat -> nat.

Theorem div_mod_axiom_div_aux_body_S :
  forall p : nat,
    connectives_equal
      (nat -> nat -> nat)
      (div_aux_body (S p))
      (fun m n : nat =>
         if Nat.leb m n
         then O
         else S (div_aux p (m - S n) n)).
Admitted.
