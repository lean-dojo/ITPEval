(*
  Statement-only formalization of Logipedia corpus artifact exp.sym_eq_exp
  (catalog title "exp.sym_eq_exp"): for all natural indices, the filtered
  exponential body is Leibniz-equal to the exponential function. This file
  contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter exp exp_body : nat -> nat -> nat.

Theorem exp_sym_eq_exp :
  forall n m : nat,
    logipedia_leibniz
      nat
      (filter_nat_type nat (exp_body n) m)
      (exp n m).
Admitted.
