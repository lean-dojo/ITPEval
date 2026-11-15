(*
  Statement-only formalization of Logipedia corpus artifact nat.axiom_times
  (catalog title "nat.axiom_times"): for every natural input, the source
  polymorphic equality relates the partially applied natural multiplication
  function to the corresponding naturally filtered multiplication body.
  This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter times times_body : nat -> nat -> nat.

Theorem logipedia_nat_axiom_times :
  forall n : nat,
    connectives_equal
      (nat -> nat)
      (times n)
      (filter_nat_type (nat -> nat) times_body n).
Admitted.
