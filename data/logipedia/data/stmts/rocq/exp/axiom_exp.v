(*
  Statement-only formalization of Logipedia corpus artifact exp.axiom_exp
  (catalog title "exp.axiom_exp"): for all natural exponents, the source
  exponential function is related by the source equality to the filtered
  exponential body. This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter exp exp_body : nat -> nat -> nat.

Theorem exp_axiom_exp :
  forall n m : nat,
    connectives_equal
      nat
      (exp n m)
      (filter_nat_type nat (exp_body n) m).
Admitted.
