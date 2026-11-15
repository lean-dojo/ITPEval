(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_times_body_S (catalog title "nat.axiom_times_body_S"): for every
  natural number, the source polymorphic equality relates the natural
  multiplication body at its successor to the function sending each natural
  number m to m plus the product of the original number and m. This file
  contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter plus times times_body : nat -> nat -> nat.

Theorem logipedia_nat_axiom_times_body_S :
  forall n : nat,
    connectives_equal
      (nat -> nat)
      (times_body (S n))
      (fun m : nat => plus m (times n m)).
Admitted.
