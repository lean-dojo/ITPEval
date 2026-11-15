(*
  Statement-only formalization of Logipedia corpus artifact nat.eq_times
  (catalog title "nat.eq_times"): for every natural input, Leibniz equality
  relates the partially applied natural multiplication function to the
  corresponding naturally filtered multiplication body. This file contains
  no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter times times_body : nat -> nat -> nat.

Theorem logipedia_nat_eq_times :
  forall n : nat,
    logipedia_leibniz
      (nat -> nat)
      (times n)
      (filter_nat_type (nat -> nat) times_body n).
Admitted.
