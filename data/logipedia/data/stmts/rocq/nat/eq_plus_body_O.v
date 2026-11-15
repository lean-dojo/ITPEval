(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_plus_body_O (catalog title "nat.eq_plus_body_O"): Leibniz equality
  relates the natural-addition body at zero to the identity function on
  natural numbers. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter plus_body : nat -> nat -> nat.

Theorem logipedia_nat_eq_plus_body_O :
  logipedia_leibniz
    (nat -> nat)
    (plus_body O)
    (fun m : nat => m).
Admitted.
