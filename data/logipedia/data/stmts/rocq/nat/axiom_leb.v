(*
  Statement-only formalization of Logipedia corpus artifact nat.axiom_leb
  (catalog title "nat.axiom_leb"): for every natural input, the source
  polymorphic equality relates the Boolean-valued less-than-or-equal test
  function to the corresponding naturally filtered comparison body. This
  file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter leb leb_body : nat -> nat -> bool.

Theorem logipedia_nat_axiom_leb :
  forall n : nat,
    connectives_equal
      (nat -> bool)
      (leb n)
      (filter_nat_type (nat -> bool) leb_body n).
Admitted.
