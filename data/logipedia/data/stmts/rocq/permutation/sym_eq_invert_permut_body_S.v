(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.sym_eq_invert_permut_body_S (catalog title
  "permutation.sym_eq_invert_permut_body_S"): for every natural index, the
  function that returns its successor when the input equals the given
  function's value there, and otherwise uses the preceding inverse
  permutation, is Leibniz-equal to the inverse-permutation body at that
  successor. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter invert_permut invert_permut_body :
  nat -> (nat -> nat) -> nat -> nat.

Theorem sym_eq_invert_permut_body_S :
  forall n : nat,
    logipedia_leibniz
      ((nat -> nat) -> nat -> nat)
      (fun (f : nat -> nat) (m : nat) =>
         if Nat.eqb m (f (S n))
         then S n
         else invert_permut n f m)
      (invert_permut_body (S n)).
Admitted.
