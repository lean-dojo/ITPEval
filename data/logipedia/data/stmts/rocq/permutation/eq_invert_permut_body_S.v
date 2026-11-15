(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.eq_invert_permut_body_S (catalog title
  "permutation.eq_invert_permut_body_S"): for every natural index, the
  inverse-permutation body at its successor is Leibniz-equal to the function
  that returns that successor when the input equals the given function's
  value there, and otherwise uses the preceding inverse permutation. This
  file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter invert_permut invert_permut_body :
  nat -> (nat -> nat) -> nat -> nat.

Theorem eq_invert_permut_body_S :
  forall n : nat,
    logipedia_leibniz
      ((nat -> nat) -> nat -> nat)
      (invert_permut_body (S n))
      (fun (f : nat -> nat) (m : nat) =>
         if Nat.eqb m (f (S n))
         then S n
         else invert_permut n f m).
Admitted.
