(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_times_body_O (catalog title "nat.eq_times_body_O"): Leibniz equality
  relates the natural-multiplication body at zero to the constant-zero
  function on natural numbers. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter times_body : nat -> nat -> nat.

Theorem logipedia_nat_eq_times_body_O :
  logipedia_leibniz
    (nat -> nat)
    (times_body O)
    (fun _ : nat => O).
Admitted.
