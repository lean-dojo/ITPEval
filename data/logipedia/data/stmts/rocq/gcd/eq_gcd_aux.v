(*
  Statement-only formalization of Logipedia corpus artifact gcd.eq_gcd_aux
  (catalog title "gcd.eq_gcd_aux"): for every natural index, the auxiliary
  gcd function is Leibniz-equal to the natural-type filter of its auxiliary
  body. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter gcd_aux gcd_aux_body : nat -> nat -> nat -> nat.

Theorem gcd_eq_gcd_aux :
  forall p : nat,
    logipedia_leibniz
      (nat -> nat -> nat)
      (gcd_aux p)
      (filter_nat_type (nat -> nat -> nat) gcd_aux_body p).
Admitted.
