(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_minus_body_S (catalog title "nat.axiom_minus_body_S"): for every
  natural number, the source polymorphic equality relates the natural
  subtraction body at its successor to the natural-number matcher with that
  successor at zero and the preceding subtraction at successors. This file
  contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter match_nat_type :
  forall return_type : Type,
    return_type -> (nat -> return_type) -> nat -> return_type.
Parameter minus minus_body : nat -> nat -> nat.

Theorem logipedia_nat_axiom_minus_body_S :
  forall n : nat,
    connectives_equal
      (nat -> nat)
      (minus_body (S n))
      (fun m : nat =>
         match_nat_type nat (S n) (fun q : nat => minus n q) m).
Admitted.
