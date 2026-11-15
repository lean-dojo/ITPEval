(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.sym_eq_gcd_aux (catalog title "gcd.sym_eq_gcd_aux"): for every natural
  index, the natural-type filter of the auxiliary gcd body is Leibniz-equal
  to the auxiliary gcd function. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter gcd_aux gcd_aux_body : nat -> nat -> nat -> nat.

Theorem gcd_sym_eq_gcd_aux :
  forall p : nat,
    logipedia_leibniz
      (nat -> nat -> nat)
      (filter_nat_type (nat -> nat -> nat) gcd_aux_body p)
      (gcd_aux p).
Admitted.
