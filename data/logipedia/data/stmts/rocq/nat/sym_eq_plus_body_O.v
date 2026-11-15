(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_plus_body_O (catalog title "nat.sym_eq_plus_body_O"): Leibniz
  equality relates the identity function on natural numbers to the
  natural-addition body at zero. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter plus_body : nat -> nat -> nat.

Theorem logipedia_nat_sym_eq_plus_body_O :
  logipedia_leibniz
    (nat -> nat)
    (fun m : nat => m)
    (plus_body O).
Admitted.
