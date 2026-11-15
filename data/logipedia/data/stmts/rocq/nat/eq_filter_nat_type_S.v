(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_filter_nat_type_S (catalog title "nat.eq_filter_nat_type_S"):
  for every result type, natural-number-indexed function, and natural number,
  Leibniz equality relates filtering the function at that number's successor
  to its value at the same successor. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.

Theorem logipedia_nat_eq_filter_nat_type_S :
  forall (return_type : Type)
         (return_ : nat -> return_type)
         (n : nat),
    logipedia_leibniz
      return_type
      (filter_nat_type return_type return_ (S n))
      (return_ (S n)).
Admitted.
