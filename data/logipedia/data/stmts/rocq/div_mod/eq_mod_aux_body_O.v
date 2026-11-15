(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.eq_mod_aux_body_O (catalog title "div_mod.eq_mod_aux_body_O"):
  Leibniz equality identifies the zero-indexed modulo auxiliary body with
  the binary natural-number function that returns its first argument.
  This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter mod_aux_body : nat -> nat -> nat -> nat.

Theorem div_mod_eq_mod_aux_body_O :
  logipedia_leibniz
    (nat -> nat -> nat)
    (mod_aux_body O)
    (fun (m _n : nat) => m).
Admitted.
