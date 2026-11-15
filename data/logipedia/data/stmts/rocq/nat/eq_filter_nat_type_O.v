(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_filter_nat_type_O (catalog title "nat.eq_filter_nat_type_O"):
  for every result type and natural-number-indexed function, Leibniz equality
  relates filtering the function at zero to its value at zero. This file
  contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.

Theorem logipedia_nat_eq_filter_nat_type_O :
  forall (return_type : Type) (return_ : nat -> return_type),
    logipedia_leibniz
      return_type
      (filter_nat_type return_type return_ O)
      (return_ O).
Admitted.
