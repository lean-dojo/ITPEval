(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_times_body_S (catalog title "nat.eq_times_body_S"): for every natural
  number, Leibniz equality relates the natural-multiplication body at its
  successor to the function sending each natural number m to m plus the
  product of the original number and m. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter plus times times_body : nat -> nat -> nat.

Theorem logipedia_nat_eq_times_body_S :
  forall n : nat,
    logipedia_leibniz
      (nat -> nat)
      (times_body (S n))
      (fun m : nat => plus m (times n m)).
Admitted.
