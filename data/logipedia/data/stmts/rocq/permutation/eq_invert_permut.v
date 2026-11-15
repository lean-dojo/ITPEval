(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.eq_invert_permut (catalog title
  "permutation.eq_invert_permut"): for every natural index, the inverse-
  permutation function is Leibniz-equal to the natural-type filtered
  inverse-permutation body. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter invert_permut invert_permut_body :
  nat -> (nat -> nat) -> nat -> nat.

Theorem permutation_eq_invert_permut :
  forall n : nat,
    logipedia_leibniz
      ((nat -> nat) -> nat -> nat)
      (invert_permut n)
      (filter_nat_type
        ((nat -> nat) -> nat -> nat)
        invert_permut_body
        n).
Admitted.
