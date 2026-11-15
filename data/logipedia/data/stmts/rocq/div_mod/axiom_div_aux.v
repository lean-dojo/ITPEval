(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.axiom_div_aux (catalog title "div_mod.axiom_div_aux"):
  at every natural index, the division auxiliary function is related by the
  source equality to the filtered division-auxiliary body. This file contains
  no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter div_aux div_aux_body : nat -> nat -> nat -> nat.

Theorem div_mod_axiom_div_aux :
  forall p : nat,
    connectives_equal
      (nat -> nat -> nat)
      (div_aux p)
      (filter_nat_type (nat -> nat -> nat) div_aux_body p).
Admitted.
