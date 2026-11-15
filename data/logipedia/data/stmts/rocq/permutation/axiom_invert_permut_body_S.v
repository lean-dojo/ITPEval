(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.axiom_invert_permut_body_S (catalog title
  "permutation.axiom_invert_permut_body_S"): for every natural index, the
  source equality relates the inverse-permutation body at its successor to
  the function that returns that successor when the input equals the given
  function's value there, and otherwise uses the preceding inverse
  permutation. This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter invert_permut invert_permut_body :
  nat -> (nat -> nat) -> nat -> nat.

Theorem permutation_axiom_invert_permut_body_S :
  forall n : nat,
    connectives_equal
      ((nat -> nat) -> nat -> nat)
      (invert_permut_body (S n))
      (fun (f : nat -> nat) (m : nat) =>
         if Nat.eqb m (f (S n))
         then S n
         else invert_permut n f m).
Admitted.
