(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_plus_body_S (catalog title "nat.sym_eq_plus_body_S"): for every
  natural number, Leibniz equality relates the function sending each natural
  number to the successor of its sum with the original number to the
  natural-addition body at the successor. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter plus plus_body : nat -> nat -> nat.

Theorem logipedia_nat_sym_eq_plus_body_S :
  forall n : nat,
    logipedia_leibniz
      (nat -> nat)
      (fun m : nat => S (plus n m))
      (plus_body (S n)).
Admitted.
