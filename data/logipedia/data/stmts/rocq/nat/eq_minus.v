(*
  Statement-only formalization of Logipedia corpus artifact nat.eq_minus
  (catalog title "nat.eq_minus"): for every natural input, Leibniz equality
  relates the partially applied natural subtraction function to the
  corresponding naturally filtered subtraction body. This file contains no
  proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter minus minus_body : nat -> nat -> nat.

Theorem logipedia_nat_eq_minus :
  forall n : nat,
    logipedia_leibniz
      (nat -> nat)
      (minus n)
      (filter_nat_type (nat -> nat) minus_body n).
Admitted.
