(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.eq_invert_permut_body_O (catalog title
  "permutation.eq_invert_permut_body_O"): the inverse-permutation auxiliary
  body at zero is Leibniz-equal to the function whose Boolean equality test
  selects zero in either branch. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter invert_permut_body :
  nat -> (nat -> nat) -> nat -> nat.

Theorem eq_invert_permut_body_O :
  logipedia_leibniz
    ((nat -> nat) -> nat -> nat)
    (invert_permut_body O)
    (fun (f : nat -> nat) (m : nat) =>
       if Nat.eqb m (f O) then O else O).
Admitted.
