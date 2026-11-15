(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_filter_nat_type_S (catalog title
  "nat.axiom_filter_nat_type_S"): for every result type,
  natural-number-indexed function, and natural number, filtering at its
  successor is related by the source polymorphic equality to the function's
  value at that successor. This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.

Theorem logipedia_nat_axiom_filter_nat_type_S :
  forall (return_type : Type)
         (return_ : nat -> return_type)
         (n : nat),
    connectives_equal
      return_type
      (filter_nat_type return_type return_ (S n))
      (return_ (S n)).
Admitted.
