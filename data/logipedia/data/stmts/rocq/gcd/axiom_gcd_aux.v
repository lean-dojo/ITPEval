(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.axiom_gcd_aux (catalog title "gcd.axiom_gcd_aux"): at every natural
  index, the auxiliary gcd function is related by the source equality to the
  natural-type filter of its auxiliary body. This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter gcd_aux gcd_aux_body : nat -> nat -> nat -> nat.

Theorem gcd_axiom_gcd_aux :
  forall p : nat,
    connectives_equal
      (nat -> nat -> nat)
      (gcd_aux p)
      (filter_nat_type (nat -> nat -> nat) gcd_aux_body p).
Admitted.
