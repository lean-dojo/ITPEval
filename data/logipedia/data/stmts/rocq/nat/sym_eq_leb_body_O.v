(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_leb_body_O (catalog title "nat.sym_eq_leb_body_O"): Leibniz
  equality relates the constant-true function on natural numbers to the
  Boolean less-than-or-equal test body at natural zero. This file contains no
  proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter leb_body : nat -> nat -> bool.

Theorem logipedia_nat_sym_eq_leb_body_O :
  logipedia_leibniz
    (nat -> bool)
    (fun _ : nat => true)
    (leb_body O).
Admitted.
