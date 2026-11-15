(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.axiom_invert_permut (catalog title
  "permutation.axiom_invert_permut"): for every natural index, the source
  equality relates the inverse-permutation function to the natural-type
  filtered inverse-permutation body. This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter invert_permut invert_permut_body :
  nat -> (nat -> nat) -> nat -> nat.

Theorem permutation_axiom_invert_permut :
  forall n : nat,
    connectives_equal
      ((nat -> nat) -> nat -> nat)
      (invert_permut n)
      (filter_nat_type
        ((nat -> nat) -> nat -> nat)
        invert_permut_body
        n).
Admitted.
