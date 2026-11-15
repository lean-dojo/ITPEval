(*
  Statement-only formalization of Logipedia corpus artifact fact.eq_fact
  (catalog title "fact.eq_fact"): for every natural input, the factorial
  function is Leibniz-equal to the filtered factorial body. This file contains
  no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter fact fact_body : nat -> nat.

Theorem fact_eq_fact :
  forall n : nat,
    logipedia_leibniz
      nat
      (fact n)
      (filter_nat_type nat fact_body n).
Admitted.
