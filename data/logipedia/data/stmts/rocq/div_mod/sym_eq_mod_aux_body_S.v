(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.sym_eq_mod_aux_body_S (catalog title
  "div_mod.sym_eq_mod_aux_body_S"): Leibniz equality identifies the binary
  natural-number function that returns its first input when it is at most its
  second, and otherwise returns mod_aux at the predecessor index after
  truncated subtraction by the second input's successor, with the
  successor-indexed modulo auxiliary body. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter mod_aux mod_aux_body : nat -> nat -> nat -> nat.

Theorem div_mod_sym_eq_mod_aux_body_S :
  forall p : nat,
    logipedia_leibniz
      (nat -> nat -> nat)
      (fun m n : nat =>
         if Nat.leb m n
         then m
         else mod_aux p (m - S n) n)
      (mod_aux_body (S p)).
Admitted.
