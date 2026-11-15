(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_plus_body_S (catalog title "nat.eq_plus_body_S"): for every natural
  number, Leibniz equality relates the natural-addition body at its successor
  to the function sending each natural number to the successor of its sum with
  the original number. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter plus plus_body : nat -> nat -> nat.

Theorem logipedia_nat_eq_plus_body_S :
  forall n : nat,
    logipedia_leibniz
      (nat -> nat)
      (plus_body (S n))
      (fun m : nat => S (plus n m)).
Admitted.
