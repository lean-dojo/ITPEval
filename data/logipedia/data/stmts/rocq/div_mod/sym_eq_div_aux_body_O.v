(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.sym_eq_div_aux_body_O (catalog title
  "div_mod.sym_eq_div_aux_body_O"): Leibniz equality identifies the
  constant-zero binary natural-number function with the zero-indexed
  division auxiliary body. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter div_aux_body : nat -> nat -> nat -> nat.

Theorem div_mod_sym_eq_div_aux_body_O :
  logipedia_leibniz
    (nat -> nat -> nat)
    (fun (_m _n : nat) => O)
    (div_aux_body O).
Admitted.
