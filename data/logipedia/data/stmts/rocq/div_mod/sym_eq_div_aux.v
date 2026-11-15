(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.sym_eq_div_aux (catalog title "div_mod.sym_eq_div_aux"): at every
  natural index, the filtered division-auxiliary body is Leibniz-equal to the
  division auxiliary function. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter div_aux div_aux_body : nat -> nat -> nat -> nat.

Theorem div_mod_sym_eq_div_aux :
  forall p : nat,
    logipedia_leibniz
      (nat -> nat -> nat)
      (filter_nat_type (nat -> nat -> nat) div_aux_body p)
      (div_aux p).
Admitted.
