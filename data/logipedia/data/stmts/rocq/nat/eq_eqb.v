(*
  Statement-only formalization of Logipedia corpus artifact nat.eq_eqb
  (catalog title "nat.eq_eqb"): for every natural input, Leibniz equality
  relates the Boolean-valued equality-test function to the corresponding
  naturally filtered equality-test body. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter eqb eqb_body : nat -> nat -> bool.

Theorem logipedia_nat_eq_eqb :
  forall n : nat,
    logipedia_leibniz
      (nat -> bool)
      (eqb n)
      (filter_nat_type (nat -> bool) eqb_body n).
Admitted.
