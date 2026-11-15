(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.sym_eq_invert_permut_body_O (catalog title
  "permutation.sym_eq_invert_permut_body_O"): the function whose Boolean
  equality test selects zero in either branch is Leibniz-equal to the
  inverse-permutation auxiliary body at zero. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter invert_permut_body :
  nat -> (nat -> nat) -> nat -> nat.

Theorem sym_eq_invert_permut_body_O :
  logipedia_leibniz
    ((nat -> nat) -> nat -> nat)
    (fun (f : nat -> nat) (m : nat) =>
       if Nat.eqb m (f O) then O else O)
    (invert_permut_body O).
Admitted.
