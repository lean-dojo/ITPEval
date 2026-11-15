(*
  Statement-only formalization of Logipedia corpus artifact exp.eq_exp
  (catalog title "exp.eq_exp"): for all natural indices, the exponential
  function is Leibniz-equal to the filtered exponential body. This file
  contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter exp exp_body : nat -> nat -> nat.

Theorem exp_eq_exp :
  forall n m : nat,
    logipedia_leibniz
      nat
      (exp n m)
      (filter_nat_type nat (exp_body n) m).
Admitted.
