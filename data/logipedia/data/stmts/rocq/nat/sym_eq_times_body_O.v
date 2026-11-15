(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_times_body_O (catalog title "nat.sym_eq_times_body_O"): Leibniz
  equality relates the constant-zero function on natural numbers to the
  natural-multiplication body at zero. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter times_body : nat -> nat -> nat.

Theorem logipedia_nat_sym_eq_times_body_O :
  logipedia_leibniz
    (nat -> nat)
    (fun _ : nat => O)
    (times_body O).
Admitted.
