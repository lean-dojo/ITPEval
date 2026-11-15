(*
  Statement-only formalization of Logipedia corpus artifact nat.sym_eq_minus
  (catalog title "nat.sym_eq_minus"): for every natural input, the filtered
  natural subtraction body is Leibniz-equal to the partially applied
  subtraction function. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter minus minus_body : nat -> nat -> nat.

Theorem nat_sym_eq_minus :
  forall n : nat,
    logipedia_leibniz
      (nat -> nat)
      (filter_nat_type (nat -> nat) minus_body n)
      (minus n).
Admitted.
