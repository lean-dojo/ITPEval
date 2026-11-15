(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_times_body_O (catalog title "nat.axiom_times_body_O"): the source
  polymorphic equality relates the natural-multiplication body at zero to the
  constant-zero function on natural numbers. This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter times_body : nat -> nat -> nat.

Theorem logipedia_nat_axiom_times_body_O :
  connectives_equal
    (nat -> nat)
    (times_body O)
    (fun _ : nat => O).
Admitted.
