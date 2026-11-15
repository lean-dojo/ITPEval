(*
  Statement-only formalization of Logipedia corpus artifact nat.eq_leb
  (catalog title "nat.eq_leb"): for every natural input, Leibniz equality
  relates the Boolean-valued less-than-or-equal test function to the
  corresponding naturally filtered comparison body. This file contains no
  proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter leb leb_body : nat -> nat -> bool.

Theorem logipedia_nat_eq_leb :
  forall n : nat,
    logipedia_leibniz
      (nat -> bool)
      (leb n)
      (filter_nat_type (nat -> bool) leb_body n).
Admitted.
