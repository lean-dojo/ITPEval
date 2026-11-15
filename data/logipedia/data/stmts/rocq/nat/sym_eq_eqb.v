(*
  Statement-only formalization of Logipedia corpus artifact nat.sym_eq_eqb
  (catalog title "nat.sym_eq_eqb"): for every natural input, the filtered
  boolean equality body is Leibniz-equal to the boolean equality function.
  This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter eqb eqb_body : nat -> nat -> bool.

Theorem nat_sym_eq_eqb :
  forall n : nat,
    logipedia_leibniz
      (nat -> bool)
      (filter_nat_type (nat -> bool) eqb_body n)
      (eqb n).
Admitted.
