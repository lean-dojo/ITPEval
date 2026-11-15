(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.eq_div_aux (catalog title "div_mod.eq_div_aux"): at every natural
  index, the division auxiliary function is Leibniz-equal to the filtered
  division-auxiliary body. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter div_aux div_aux_body : nat -> nat -> nat -> nat.

Theorem div_mod_eq_div_aux :
  forall p : nat,
    logipedia_leibniz
      (nat -> nat -> nat)
      (div_aux p)
      (filter_nat_type (nat -> nat -> nat) div_aux_body p).
Admitted.
