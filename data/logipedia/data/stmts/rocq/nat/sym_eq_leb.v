(*
  Statement-only formalization of Logipedia corpus artifact nat.sym_eq_leb
  (catalog title "nat.sym_eq_leb"): for every natural input, the filtered
  Boolean-valued less-than-or-equal body is Leibniz-equal to the
  less-than-or-equal test function. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter leb leb_body : nat -> nat -> bool.

Theorem nat_sym_eq_leb :
  forall n : nat,
    logipedia_leibniz
      (nat -> bool)
      (filter_nat_type (nat -> bool) leb_body n)
      (leb n).
Admitted.
