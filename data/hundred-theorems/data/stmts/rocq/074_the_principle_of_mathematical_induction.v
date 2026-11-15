(*
  Statement-only formalization of Hundred Theorems item 074,
  "The Principle of Mathematical Induction": a predicate on natural numbers
  that holds at zero and is preserved by successor holds for every natural
  number. This file contains no proof.
*)

From Corelib Require Export Datatypes.

Theorem principle_of_mathematical_induction :
  forall P : nat -> Prop,
    P O ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.
Admitted.
