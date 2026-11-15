(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.axiom_invert_permut_body_O (catalog title
  "permutation.axiom_invert_permut_body_O"): the source equality relates the
  inverse-permutation body at zero to the function returning zero after
  testing whether its input equals the given function's value at zero. This
  file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter invert_permut_body :
  nat -> (nat -> nat) -> nat -> nat.

Theorem permutation_axiom_invert_permut_body_O :
  connectives_equal
    ((nat -> nat) -> nat -> nat)
    (invert_permut_body O)
    (fun (f : nat -> nat) (m : nat) =>
       if Nat.eqb m (f O) then O else O).
Admitted.
