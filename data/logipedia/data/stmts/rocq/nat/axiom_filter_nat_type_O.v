(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_filter_nat_type_O (catalog title
  "nat.axiom_filter_nat_type_O"): for every result type and
  natural-number-indexed function, filtering at zero is related by the
  source polymorphic equality to the function's value at zero. This file
  contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.

Theorem logipedia_nat_axiom_filter_nat_type_O :
  forall (return_type : Type) (return_ : nat -> return_type),
    connectives_equal
      return_type
      (filter_nat_type return_type return_ O)
      (return_ O).
Admitted.
