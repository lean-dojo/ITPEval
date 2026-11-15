(*
  Statement-only formalization of Logipedia corpus artifact fact.sym_eq_fact
  (catalog title "fact.sym_eq_fact"): for every natural input, the filtered
  factorial body is Leibniz-equal to the factorial function. This file
  contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter fact fact_body : nat -> nat.

Theorem fact_sym_eq_fact :
  forall n : nat,
    logipedia_leibniz
      nat
      (filter_nat_type nat fact_body n)
      (fact n).
Admitted.
