(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_plus_body_S (catalog title "nat.axiom_plus_body_S"): for every
  natural number, the source polymorphic equality relates the natural-addition
  body at its successor to the function sending each natural number to the
  successor of its sum with the original number. This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter plus plus_body : nat -> nat -> nat.

Theorem logipedia_nat_axiom_plus_body_S :
  forall n : nat,
    connectives_equal
      (nat -> nat)
      (plus_body (S n))
      (fun m : nat => S (plus n m)).
Admitted.
